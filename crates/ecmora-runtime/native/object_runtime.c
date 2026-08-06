#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <math.h>

typedef enum {
    ECMORA_UNDEFINED = 0,
    ECMORA_NULL = 1,
    ECMORA_NUMBER = 2,
    ECMORA_BOOL = 3,
    ECMORA_STRING = 4,
    ECMORA_OBJECT = 5,
    ECMORA_CALLABLE = 6,
    ECMORA_PROMISE = 7,
    ECMORA_CELL = 8
} EcmoraTag;

typedef union {
    double number;
    bool boolean;
    void *pointer;
} EcmoraPayload;

typedef struct EcmoraProperty {
    char *key;
    EcmoraTag tag;
    EcmoraPayload payload;
    void *getter;
    void *setter;
    bool enumerable;
    bool configurable;
    bool writable;
    struct EcmoraProperty *next;
} EcmoraProperty;

typedef struct {
    EcmoraProperty *head;
    void *prototype;
} EcmoraObject;

typedef struct {
    uint8_t tag;
    uint64_t payload;
} EcmoraValue;

typedef uint8_t (*EcmoraCode)(
    void *closure,
    uint32_t argc,
    EcmoraValue *argv,
    EcmoraValue *out
);

typedef struct {
    EcmoraCode code;
    uint32_t capture_count;
    EcmoraValue captures[];
} EcmoraClosure;

typedef enum {
    ECMORA_PROMISE_PENDING = 0,
    ECMORA_PROMISE_FULFILLED = 1,
    ECMORA_PROMISE_REJECTED = 2
} EcmoraPromiseState;

typedef struct EcmoraPromise EcmoraPromise;
typedef struct EcmoraPromiseReaction EcmoraPromiseReaction;

struct EcmoraPromise {
    EcmoraPromiseState state;
    EcmoraValue result;
    EcmoraPromiseReaction *reactions_head;
    EcmoraPromiseReaction *reactions_tail;
};

struct EcmoraPromiseReaction {
    EcmoraClosure *on_fulfilled;
    EcmoraClosure *on_rejected;
    EcmoraPromise *next;
    EcmoraPromiseReaction *next_reaction;
};

typedef struct EcmoraPromiseJob {
    EcmoraPromiseState state;
    EcmoraValue argument;
    EcmoraClosure *handler;
    EcmoraPromise *next;
    struct EcmoraPromiseJob *next_job;
} EcmoraPromiseJob;

static EcmoraPromiseJob *microtask_head = NULL;
static EcmoraPromiseJob *microtask_tail = NULL;


void *ecmora_closure_new(void *code, uint32_t capture_count, EcmoraValue *captures) {
    size_t size = sizeof(EcmoraClosure) + sizeof(EcmoraValue) * capture_count;
    EcmoraClosure *closure = (EcmoraClosure *)calloc(1, size);
    if (closure == NULL) abort();
    closure->code = (EcmoraCode)code;
    closure->capture_count = capture_count;
    if (capture_count != 0) {
        memcpy(closure->captures, captures, sizeof(EcmoraValue) * capture_count);
    }
    return closure;
}

void ecmora_closure_capture(void *pointer, uint32_t index, EcmoraValue *out) {
    EcmoraClosure *closure = (EcmoraClosure *)pointer;
    if (closure == NULL || index >= closure->capture_count) {
        if (out != NULL) *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return;
    }
    if (out != NULL) *out = closure->captures[index];
}

void ecmora_argument_get(
    uint32_t argc,
    const EcmoraValue *argv,
    uint32_t index,
    EcmoraValue *out
) {
    if (out == NULL) return;
    if (argv == NULL || index >= argc) {
        *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return;
    }
    *out = argv[index];
}

#if defined(_MSC_VER)
__declspec(thread) static EcmoraValue *ecmora_tail_argv_buffer = NULL;
__declspec(thread) static uint32_t ecmora_tail_argv_capacity = 0;
#else
static _Thread_local EcmoraValue *ecmora_tail_argv_buffer = NULL;
static _Thread_local uint32_t ecmora_tail_argv_capacity = 0;
#endif

EcmoraValue *ecmora_tail_argv_reserve(uint32_t count) {
    if (count == 0) return NULL;
    if (count > ecmora_tail_argv_capacity) {
        EcmoraValue *grown = (EcmoraValue *)realloc(
            ecmora_tail_argv_buffer,
            sizeof(EcmoraValue) * (size_t)count
        );
        if (grown == NULL) abort();
        ecmora_tail_argv_buffer = grown;
        ecmora_tail_argv_capacity = count;
    }
    return ecmora_tail_argv_buffer;
}

uint8_t ecmora_closure_call(
    void *pointer,
    uint32_t argc,
    EcmoraValue *argv,
    EcmoraValue *out
) {
    if (out != NULL) {
        *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
    }

    EcmoraClosure *closure = (EcmoraClosure *)pointer;
    if (closure == NULL || closure->code == NULL || (argc != 0 && argv == NULL)) {
        /*
         * Status 1 is ThrowCompletion in the native ABI. Until Error objects
         * are materialized, undefined is the temporary thrown payload.
         */
        return 1;
    }
    return closure->code(closure, argc, argv, out);
}

void *ecmora_cell_new(const EcmoraValue *initial) {
    EcmoraValue *cell = (EcmoraValue *)malloc(sizeof(EcmoraValue));
    if (cell == NULL) abort();
    *cell = initial == NULL ? (EcmoraValue){ ECMORA_UNDEFINED, 0 } : *initial;
    return cell;
}

void ecmora_cell_get(void *pointer, EcmoraValue *out) {
    if (pointer == NULL) {
        if (out != NULL) *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return;
    }
    if (out != NULL) *out = *(EcmoraValue *)pointer;
}

void ecmora_cell_set(void *pointer, const EcmoraValue *value) {
    if (pointer != NULL && value != NULL) *(EcmoraValue *)pointer = *value;
}

static EcmoraValue ecmora_undefined_value(void) {
    return (EcmoraValue){ ECMORA_UNDEFINED, 0 };
}

static EcmoraPromise *ecmora_promise_allocate(void) {
    EcmoraPromise *promise = (EcmoraPromise *)calloc(1, sizeof(EcmoraPromise));
    if (promise == NULL) abort();
    promise->state = ECMORA_PROMISE_PENDING;
    promise->result = ecmora_undefined_value();
    return promise;
}

static void ecmora_enqueue_promise_job(
    EcmoraPromiseState state,
    EcmoraValue argument,
    EcmoraClosure *handler,
    EcmoraPromise *next
) {
    EcmoraPromiseJob *job = (EcmoraPromiseJob *)calloc(1, sizeof(EcmoraPromiseJob));
    if (job == NULL) abort();
    job->state = state;
    job->argument = argument;
    job->handler = handler;
    job->next = next;
    if (microtask_tail == NULL) {
        microtask_head = job;
    } else {
        microtask_tail->next_job = job;
    }
    microtask_tail = job;
}

static void ecmora_promise_append_reaction(
    EcmoraPromise *source,
    EcmoraClosure *on_fulfilled,
    EcmoraClosure *on_rejected,
    EcmoraPromise *next
) {
    EcmoraPromiseReaction *reaction =
        (EcmoraPromiseReaction *)calloc(1, sizeof(EcmoraPromiseReaction));
    if (reaction == NULL) abort();
    reaction->on_fulfilled = on_fulfilled;
    reaction->on_rejected = on_rejected;
    reaction->next = next;
    if (source->reactions_tail == NULL) {
        source->reactions_head = reaction;
    } else {
        source->reactions_tail->next_reaction = reaction;
    }
    source->reactions_tail = reaction;
}

static void ecmora_trigger_promise_reactions(EcmoraPromise *promise) {
    EcmoraPromiseReaction *reaction = promise->reactions_head;
    promise->reactions_head = NULL;
    promise->reactions_tail = NULL;
    while (reaction != NULL) {
        EcmoraPromiseReaction *next_reaction = reaction->next_reaction;
        EcmoraClosure *handler =
            promise->state == ECMORA_PROMISE_FULFILLED
                ? reaction->on_fulfilled
                : reaction->on_rejected;
        ecmora_enqueue_promise_job(
            promise->state,
            promise->result,
            handler,
            reaction->next
        );
        free(reaction);
        reaction = next_reaction;
    }
}

static void ecmora_reject_promise(EcmoraPromise *promise, EcmoraValue reason) {
    if (promise == NULL || promise->state != ECMORA_PROMISE_PENDING) return;
    promise->state = ECMORA_PROMISE_REJECTED;
    promise->result = reason;
    ecmora_trigger_promise_reactions(promise);
}

static void ecmora_fulfill_promise(EcmoraPromise *promise, EcmoraValue value) {
    if (promise == NULL || promise->state != ECMORA_PROMISE_PENDING) return;
    promise->state = ECMORA_PROMISE_FULFILLED;
    promise->result = value;
    ecmora_trigger_promise_reactions(promise);
}

static void ecmora_resolve_promise(EcmoraPromise *promise, EcmoraValue resolution) {
    if (promise == NULL || promise->state != ECMORA_PROMISE_PENDING) return;

    if (resolution.tag == ECMORA_PROMISE && resolution.payload != 0) {
        EcmoraPromise *source = (EcmoraPromise *)(uintptr_t)resolution.payload;
        if (source == promise) {
            /*
             * The full engine will materialize a TypeError object. Until the
             * Error object model exists, preserve rejection completion rather
             * than hanging or fulfilling with self.
             */
            ecmora_reject_promise(promise, ecmora_undefined_value());
            return;
        }
        if (source->state == ECMORA_PROMISE_PENDING) {
            /*
             * Null handlers implement the identity/thrower defaults. The
             * capability promise adopts whichever state source eventually has.
             */
            ecmora_promise_append_reaction(source, NULL, NULL, promise);
            return;
        }
        if (source->state == ECMORA_PROMISE_REJECTED) {
            ecmora_reject_promise(promise, source->result);
        } else {
            ecmora_fulfill_promise(promise, source->result);
        }
        return;
    }

    /*
     * Dynamically shaped object thenables are rejected by native analysis and
     * compiled through the compatibility runtime. Reaching this C fallback
     * therefore means the value is proven non-thenable or primitive.
     */
    ecmora_fulfill_promise(promise, resolution);
}

void *ecmora_promise_resolved(const EcmoraValue *value) {
    EcmoraPromise *promise = ecmora_promise_allocate();
    ecmora_resolve_promise(
        promise,
        value == NULL ? ecmora_undefined_value() : *value
    );
    return promise;
}

void *ecmora_promise_rejected(const EcmoraValue *reason) {
    EcmoraPromise *promise = ecmora_promise_allocate();
    ecmora_reject_promise(
        promise,
        reason == NULL ? ecmora_undefined_value() : *reason
    );
    return promise;
}

void *ecmora_promise_pending(void) {
    return ecmora_promise_allocate();
}

void ecmora_promise_settle(
    void *promise_pointer,
    bool rejected,
    const EcmoraValue *value
) {
    EcmoraPromise *promise = (EcmoraPromise *)promise_pointer;
    EcmoraValue settlement =
        value == NULL ? ecmora_undefined_value() : *value;
    if (rejected) {
        ecmora_reject_promise(promise, settlement);
    } else {
        ecmora_resolve_promise(promise, settlement);
    }
}

void *ecmora_promise_then(
    void *source_pointer,
    void *on_fulfilled_pointer,
    void *on_rejected_pointer
) {
    EcmoraPromise *source = (EcmoraPromise *)source_pointer;
    EcmoraPromise *next = ecmora_promise_allocate();
    if (source == NULL) {
        ecmora_reject_promise(next, ecmora_undefined_value());
        return next;
    }

    EcmoraClosure *on_fulfilled = (EcmoraClosure *)on_fulfilled_pointer;
    EcmoraClosure *on_rejected = (EcmoraClosure *)on_rejected_pointer;
    if (source->state == ECMORA_PROMISE_PENDING) {
        ecmora_promise_append_reaction(
            source,
            on_fulfilled,
            on_rejected,
            next
        );
    } else {
        EcmoraClosure *handler =
            source->state == ECMORA_PROMISE_FULFILLED
                ? on_fulfilled
                : on_rejected;
        ecmora_enqueue_promise_job(
            source->state,
            source->result,
            handler,
            next
        );
    }
    return next;
}

void ecmora_microtask_drain(void) {
    while (microtask_head != NULL) {
        EcmoraPromiseJob *job = microtask_head;
        microtask_head = job->next_job;
        if (microtask_head == NULL) microtask_tail = NULL;

        if (job->next != NULL) {
            if (job->handler == NULL) {
                if (job->state == ECMORA_PROMISE_REJECTED) {
                    ecmora_reject_promise(job->next, job->argument);
                } else {
                    ecmora_fulfill_promise(job->next, job->argument);
                }
            } else {
                EcmoraValue output = ecmora_undefined_value();
                EcmoraValue argument = job->argument;
                uint8_t completion =
                    ecmora_closure_call(job->handler, 1, &argument, &output);
                if (completion == 1) {
                    ecmora_reject_promise(job->next, output);
                } else {
                    ecmora_resolve_promise(job->next, output);
                }
            }
        }
        free(job);
    }
}


static char *copy_string(const char *source) {
    size_t length = strlen(source) + 1;
    char *copy = (char *)malloc(length);
    if (copy != NULL) memcpy(copy, source, length);
    return copy;
}

static EcmoraProperty *find_property(EcmoraObject *object, const char *key) {
    if (object == NULL) return NULL;
    for (EcmoraProperty *property = object->head; property != NULL; property = property->next) {
        if (strcmp(property->key, key) == 0) return property;
    }
    if (object->prototype != NULL) {
        return find_property((EcmoraObject *)object->prototype, key);
    }
    return NULL;
}

static EcmoraProperty *find_own_property(EcmoraObject *object, const char *key) {
    if (object == NULL) return NULL;
    for (EcmoraProperty *property = object->head; property != NULL; property = property->next) {
        if (strcmp(property->key, key) == 0) return property;
    }
    return NULL;
}

static EcmoraProperty *get_or_insert(EcmoraObject *object, const char *key) {
    EcmoraProperty *property = find_own_property(object, key);
    if (property != NULL) return property;
    property = (EcmoraProperty *)calloc(1, sizeof(EcmoraProperty));
    if (property == NULL) abort();
    property->key = copy_string(key);
    if (property->key == NULL) abort();
    property->enumerable = true;
    property->configurable = true;
    property->writable = true;
    property->next = object->head;
    object->head = property;
    return property;
}

void ecmora_object_define_accessor(void *pointer, const char *key, void *getter,
                                   void *setter, bool enumerable, bool configurable) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->configurable &&
        (property->enumerable != enumerable || configurable ||
         (getter != NULL && property->getter != getter) ||
         (setter != NULL && property->setter != setter))) {
        return;
    }
    if (getter != NULL) property->getter = getter;
    if (setter != NULL) property->setter = setter;
    property->enumerable = enumerable;
    property->configurable = configurable;
    property->writable = false;
}

void *ecmora_object_new(void) {
    EcmoraObject *object = (EcmoraObject *)calloc(1, sizeof(EcmoraObject));
    if (object == NULL) abort();
    return object;
}

void *ecmora_object_new_with_prototype(void *prototype) {
    EcmoraObject *object = (EcmoraObject *)ecmora_object_new();
    object->prototype = prototype;
    return object;
}

void ecmora_object_set_prototype(void *pointer, void *prototype) {
    if (pointer == NULL) return;
    for (EcmoraObject *cursor = (EcmoraObject *)prototype; cursor != NULL;
         cursor = (EcmoraObject *)cursor->prototype) {
        if (cursor == (EcmoraObject *)pointer) return;
    }
    ((EcmoraObject *)pointer)->prototype = prototype;
}

void *ecmora_object_get_prototype(void *pointer) {
    return pointer == NULL ? NULL : ((EcmoraObject *)pointer)->prototype;
}


bool ecmora_object_get_value(
    void *pointer,
    const char *key,
    EcmoraValue *out
) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    if (out == NULL) return property != NULL;
    if (property == NULL) {
        *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return false;
    }
    out->tag = (uint8_t)property->tag;
    switch (property->tag) {
        case ECMORA_NUMBER:
            memcpy(&out->payload, &property->payload.number, sizeof(double));
            break;
        case ECMORA_BOOL:
            out->payload = property->payload.boolean ? 1 : 0;
            break;
        case ECMORA_UNDEFINED:
        case ECMORA_NULL:
            out->payload = 0;
            break;
        default:
            out->payload = (uint64_t)(uintptr_t)property->payload.pointer;
            break;
    }
    return true;
}

void ecmora_object_set_value(
    void *pointer,
    const char *key,
    const EcmoraValue *value
) {
    if (pointer == NULL || value == NULL) return;
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = (EcmoraTag)value->tag;
    switch ((EcmoraTag)value->tag) {
        case ECMORA_NUMBER:
            memcpy(&property->payload.number, &value->payload, sizeof(double));
            break;
        case ECMORA_BOOL:
            property->payload.boolean = value->payload != 0;
            break;
        default:
            property->payload.pointer = (void *)(uintptr_t)value->payload;
            break;
    }
}

double ecmora_object_get_number(void *pointer, const char *key) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    return property == NULL ? 0.0 : property->payload.number;
}

void ecmora_object_set_number(void *pointer, const char *key, double value) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_NUMBER;
    property->payload.number = value;
}

bool ecmora_object_get_bool(void *pointer, const char *key) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    return property != NULL && property->payload.boolean;
}

void ecmora_object_set_bool(void *pointer, const char *key, bool value) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_BOOL;
    property->payload.boolean = value;
}

void *ecmora_object_get_string(void *pointer, const char *key) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    return property == NULL ? NULL : property->payload.pointer;
}

void ecmora_object_set_string(void *pointer, const char *key, void *value) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_STRING;
    property->payload.pointer = value;
}

void ecmora_object_set_undefined(void *pointer, const char *key) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_UNDEFINED;
    property->payload.pointer = NULL;
}

void ecmora_object_set_null(void *pointer, const char *key) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_NULL;
    property->payload.pointer = NULL;
}

bool ecmora_object_delete(void *pointer, const char *key) {
    EcmoraObject *object = (EcmoraObject *)pointer;
    EcmoraProperty **cursor = &object->head;
    while (*cursor != NULL) {
        EcmoraProperty *property = *cursor;
        if (strcmp(property->key, key) == 0) {
            if (!property->configurable) return false;
            *cursor = property->next;
            free(property->key);
            free(property);
            return true;
        }
        cursor = &property->next;
    }
    return true;
}


static const char *ecmora_skip_space(const char *text) {
    while (*text == ' ' || *text == '\t' || *text == '\n' || *text == '\r'
           || *text == '\f' || *text == '\v') {
        text += 1;
    }
    return text;
}

static double ecmora_parse_primitive_number(const char *text) {
    if (text == NULL) return 0.0;
    text = ecmora_skip_space(text);
    size_t length = strlen(text);
    while (length != 0) {
        char tail = text[length - 1];
        if (tail == ' ' || tail == '\t' || tail == '\n' || tail == '\r'
            || tail == '\f' || tail == '\v') {
            length -= 1;
        } else {
            break;
        }
    }
    if (length == 0) return 0.0;

    char *copy = (char *)malloc(length + 1);
    if (copy == NULL) abort();
    memcpy(copy, text, length);
    copy[length] = '\0';

    if (strcmp(copy, "Infinity") == 0 || strcmp(copy, "+Infinity") == 0) {
        free(copy);
        return INFINITY;
    }
    if (strcmp(copy, "-Infinity") == 0) {
        free(copy);
        return -INFINITY;
    }

    const char *digits = copy;
    int radix = 10;
    if (length > 2 && copy[0] == '0') {
        if (copy[1] == 'x' || copy[1] == 'X') {
            radix = 16;
            digits += 2;
        } else if (copy[1] == 'o' || copy[1] == 'O') {
            radix = 8;
            digits += 2;
        } else if (copy[1] == 'b' || copy[1] == 'B') {
            radix = 2;
            digits += 2;
        }
    }

    double result;
    if (radix != 10) {
        if (*digits == '\0') {
            result = NAN;
        } else {
            result = 0.0;
            for (const char *cursor = digits; *cursor != '\0'; cursor += 1) {
                int digit;
                if (*cursor >= '0' && *cursor <= '9') {
                    digit = *cursor - '0';
                } else if (*cursor >= 'a' && *cursor <= 'f') {
                    digit = *cursor - 'a' + 10;
                } else if (*cursor >= 'A' && *cursor <= 'F') {
                    digit = *cursor - 'A' + 10;
                } else {
                    result = NAN;
                    break;
                }
                if (digit >= radix) {
                    result = NAN;
                    break;
                }
                result = result * radix + digit;
            }
        }
    } else {
        bool valid = true;
        for (const char *cursor = copy; *cursor != '\0'; cursor += 1) {
            if (!((*cursor >= '0' && *cursor <= '9')
                  || *cursor == '.'
                  || *cursor == 'e'
                  || *cursor == 'E'
                  || *cursor == '+'
                  || *cursor == '-')) {
                valid = false;
                break;
            }
        }
        char *end = NULL;
        result = valid ? strtod(copy, &end) : NAN;
        if (!valid || end == copy || *end != '\0') result = NAN;
    }
    free(copy);
    return result;
}

double ecmora_primitive_to_number(uint8_t tag, uint64_t payload) {
    switch (tag) {
        case ECMORA_UNDEFINED:
            return NAN;
        case ECMORA_NULL:
            return 0.0;
        case ECMORA_NUMBER: {
            double number;
            memcpy(&number, &payload, sizeof(number));
            return number;
        }
        case ECMORA_BOOL:
            return payload == 0 ? 0.0 : 1.0;
        case ECMORA_STRING:
            return ecmora_parse_primitive_number(
                payload == 0 ? "" : (const char *)(uintptr_t)payload
            );
        default:
            fputs(
                "Ecmora native ToNumber received object/BigInt-capable dynamic value\n",
                stderr
            );
            abort();
    }
}

bool ecmora_dynamic_to_bool(uint8_t tag, uint64_t payload) {
    if (tag == 0 || tag == 1) return false;
    if (tag == 3) return payload != 0;
    if (tag == 2) {
        double number;
        memcpy(&number, &payload, sizeof(number));
        return number != 0.0 && number == number;
    }
    if (tag == 4) return payload != 0;
    return true;
}

static void ecmora_fprint_dynamic(FILE *stream, uint8_t tag, uint64_t payload) {
    switch (tag) {
        case ECMORA_UNDEFINED: fputs("undefined", stream); break;
        case ECMORA_NULL: fputs("null", stream); break;
        case ECMORA_NUMBER: {
            double number;
            memcpy(&number, &payload, sizeof(number));
            fprintf(stream, "%.15g", number);
            break;
        }
        case ECMORA_BOOL: fputs(payload ? "true" : "false", stream); break;
        case ECMORA_STRING:
            fputs(payload ? (const char *)((uintptr_t)payload) : "", stream);
            break;
        case ECMORA_OBJECT: fputs("[object Object]", stream); break;
        case ECMORA_CALLABLE: fputs("function () { [native code] }", stream); break;
        case ECMORA_PROMISE: fputs("[object Promise]", stream); break;
        case ECMORA_CELL: fputs("[object Cell]", stream); break;
        default: fputs("undefined", stream); break;
    }
}

void ecmora_print_dynamic(uint8_t tag, uint64_t payload) {
    ecmora_fprint_dynamic(stdout, tag, payload);
}

void ecmora_throw_uncaught(uint8_t tag, uint64_t payload) {
    fputs("Uncaught ", stderr);
    ecmora_fprint_dynamic(stderr, tag, payload);
    fputc('\n', stderr);
    fflush(stderr);
    abort();
}

#if defined(_MSC_VER)
__declspec(thread) static uint32_t ecmora_recursion_depth = 0;
#else
static _Thread_local uint32_t ecmora_recursion_depth = 0;
#endif

void ecmora_recursion_enter(const char *function_name, uint32_t limit) {
    if (ecmora_recursion_depth >= limit) {
        fprintf(
            stderr,
            "Ecmora RangeError: maximum native recursion depth (%u) exceeded in %s\n",
            limit,
            function_name == NULL ? "<anonymous>" : function_name
        );
        fflush(stderr);
        abort();
    }
    ecmora_recursion_depth += 1;
}

void ecmora_recursion_leave(void) {
    if (ecmora_recursion_depth != 0) {
        ecmora_recursion_depth -= 1;
    }
}

/* callable ABI primitive object hooks */
void *ecmora_object_new(void) {
    EcmoraObject *object = (EcmoraObject *)calloc(1, sizeof(EcmoraObject));
    if (object == NULL) abort();
    return object;
}

void ecmora_object_set_index(void *pointer, uint32_t index, const EcmoraValue *value) {
    char key[32];
    (void)snprintf(key, sizeof(key), "%u", index);
    ecmora_object_set(pointer, key, value);
    EcmoraValue length = { ECMORA_NUMBER, 0 };
    double numeric_length = (double)(index + 1);
    memcpy(&length.payload, &numeric_length, sizeof(double));
    ecmora_object_set(pointer, "length", &length);
}

uint32_t ecmora_object_length(void *pointer) {
    EcmoraValue value = { ECMORA_UNDEFINED, 0 };
    ecmora_object_get(pointer, "length", &value);
    if (value.tag != ECMORA_NUMBER) return 0;
    double length = 0.0;
    memcpy(&length, &value.payload, sizeof(double));
    if (length <= 0.0) return 0;
    if (length >= (double)UINT32_MAX) return UINT32_MAX;
    return (uint32_t)length;
}

bool ecmora_object_get_index(void *pointer, uint32_t index, EcmoraValue *out) {
    char key[32];
    (void)snprintf(key, sizeof(key), "%u", index);
    ecmora_object_get(pointer, key, out);
    return out != NULL && out->tag != ECMORA_UNDEFINED;
}
