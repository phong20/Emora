#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>

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

typedef void (*EcmoraCode)(void *closure, uint32_t argc, EcmoraValue *argv, EcmoraValue *out);

typedef struct {
    EcmoraCode code;
    uint32_t capture_count;
    EcmoraValue captures[];
} EcmoraClosure;

typedef struct {
    bool settled;
    EcmoraValue value;
} EcmoraPromise;

typedef struct EcmoraPromiseJob {
    EcmoraPromise *source;
    EcmoraPromise *next;
    EcmoraClosure *callback;
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

void ecmora_closure_call(void *pointer, uint32_t argc, EcmoraValue *argv, EcmoraValue *out) {
    EcmoraClosure *closure = (EcmoraClosure *)pointer;
    if (closure == NULL || closure->code == NULL) {
        if (out != NULL) *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return;
    }
    closure->code(closure, argc, argv, out);
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

void *ecmora_promise_resolved(const EcmoraValue *value) {
    EcmoraPromise *promise = (EcmoraPromise *)calloc(1, sizeof(EcmoraPromise));
    if (promise == NULL) abort();
    promise->settled = true;
    promise->value = value == NULL ? (EcmoraValue){ ECMORA_UNDEFINED, 0 } : *value;
    return promise;
}

void *ecmora_promise_pending(void) {
    EcmoraPromise *promise = (EcmoraPromise *)calloc(1, sizeof(EcmoraPromise));
    if (promise == NULL) abort();
    promise->settled = false;
    promise->value = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
    return promise;
}

void *ecmora_promise_then(void *source_pointer, void *callback_pointer) {
    EcmoraPromise *source = (EcmoraPromise *)source_pointer;
    EcmoraPromise *next = (EcmoraPromise *)ecmora_promise_pending();
    EcmoraPromiseJob *job = (EcmoraPromiseJob *)calloc(1, sizeof(EcmoraPromiseJob));
    if (job == NULL) abort();
    job->source = source;
    job->next = next;
    job->callback = (EcmoraClosure *)callback_pointer;
    if (microtask_tail == NULL) microtask_head = job;
    else microtask_tail->next_job = job;
    microtask_tail = job;
    return next;
}

void ecmora_microtask_drain(void) {
    while (microtask_head != NULL) {
        EcmoraPromiseJob *job = microtask_head;
        microtask_head = job->next_job;
        if (microtask_head == NULL) microtask_tail = NULL;
        EcmoraValue output = { ECMORA_UNDEFINED, 0 };
        if (job->source != NULL && job->source->settled && job->callback != NULL) {
            EcmoraValue argument = job->source->value;
            ecmora_closure_call(job->callback, 1, &argument, &output);
        }
        if (job->next != NULL) {
            job->next->settled = true;
            job->next->value = output;
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

void ecmora_print_dynamic(uint8_t tag, uint64_t payload) {
    switch (tag) {
        case 0: fputs("undefined", stdout); break;
        case 1: fputs("null", stdout); break;
        case 2: { double number; memcpy(&number, &payload, sizeof(number)); printf("%.15g", number); break; }
        case 3: fputs(payload ? "true" : "false", stdout); break;
        case 4: fputs(payload ? (const char *)((uintptr_t)payload) : "", stdout); break;
        case 5: fputs("[object Object]", stdout); break;
        case 6: fputs("function () { [native code] }", stdout); break;
        case 7: fputs("[object Promise]", stdout); break;
        default: fputs("undefined", stdout); break;
    }
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
