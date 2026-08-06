#include "callable_abi.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

enum {
    ECMORA_UNDEFINED = 0,
    ECMORA_NULL = 1,
    ECMORA_NUMBER = 2,
    ECMORA_BOOL = 3,
    ECMORA_STRING = 4,
    ECMORA_OBJECT = 5,
    ECMORA_CALLABLE = 6,
    ECMORA_PROMISE = 7,
    ECMORA_CELL = 8
};

#define ECMORA_CALLABLE_MAGIC UINT64_C(0x45434d4f52414341)

typedef uint8_t (*EcmoraCode)(
    void *closure,
    uint32_t argc,
    EcmoraValue *argv,
    EcmoraValue *out
);

typedef enum {
    ECMORA_CALLABLE_NATIVE = 1,
    ECMORA_CALLABLE_BOUND = 2
} EcmoraCallableKind;

typedef struct EcmoraCallable {
    uint64_t magic;
    EcmoraCallableKind kind;
    EcmoraCode code;
    uint32_t flags;
    uint32_t capture_count;
    EcmoraValue *captures;
    EcmoraValue lexical_this;
    EcmoraValue target;
    EcmoraValue bound_this;
    uint32_t bound_argc;
    EcmoraValue *bound_argv;
    void *prototype;
} EcmoraCallable;

typedef struct InvocationFrame {
    EcmoraValue this_value;
    EcmoraValue new_target;
    EcmoraCallable *callable;
    bool constructing;
    struct InvocationFrame *previous;
} InvocationFrame;

typedef struct {
    EcmoraValue *values;
    uint32_t length;
    uint32_t capacity;
} ArgvBuilder;

#if defined(_MSC_VER)
__declspec(thread) static InvocationFrame *ecmora_invocation_top = NULL;
#else
static _Thread_local InvocationFrame *ecmora_invocation_top = NULL;
#endif

extern void *ecmora_object_new(void);
extern void *ecmora_object_new_with_prototype(void *prototype);
extern void *ecmora_object_get_prototype(void *object);
extern bool ecmora_object_get_value(
    void *object,
    const char *key,
    EcmoraValue *out
);
extern void ecmora_object_set_value(
    void *object,
    const char *key,
    const EcmoraValue *value
);
extern bool ecmora_object_delete(void *object, const char *key);
extern void ecmora_object_set_index(
    void *object,
    uint32_t index,
    const EcmoraValue *value
);
extern uint32_t ecmora_object_length(void *object);
extern bool ecmora_object_get_index(
    void *object,
    uint32_t index,
    EcmoraValue *out
);
extern double ecmora_primitive_to_number(uint8_t tag, uint64_t payload);

static EcmoraValue ecmora_undefined(void) {
    EcmoraValue value = { ECMORA_UNDEFINED, 0 };
    return value;
}


static EcmoraValue ecmora_bool(bool input) {
    EcmoraValue value = { ECMORA_BOOL, input ? 1u : 0u };
    return value;
}

static EcmoraValue ecmora_number(double input) {
    EcmoraValue value = { ECMORA_NUMBER, 0 };
    memcpy(&value.payload, &input, sizeof(input));
    return value;
}

static EcmoraValue ecmora_pointer(uint8_t tag, void *pointer) {
    EcmoraValue value = { tag, (uint64_t)(uintptr_t)pointer };
    return value;
}

static double ecmora_number_value(EcmoraValue value) {
    double output = 0.0;
    memcpy(&output, &value.payload, sizeof(output));
    return output;
}

static bool ecmora_is_object_like(EcmoraValue value) {
    return value.payload != 0
        && (value.tag == ECMORA_OBJECT
            || value.tag == ECMORA_CALLABLE
            || value.tag == ECMORA_PROMISE);
}

static EcmoraCallable *ecmora_as_callable(EcmoraValue value) {
    if (value.tag != ECMORA_CALLABLE || value.payload == 0) return NULL;
    EcmoraCallable *callable = (EcmoraCallable *)(uintptr_t)value.payload;
    return callable->magic == ECMORA_CALLABLE_MAGIC ? callable : NULL;
}

static void ecmora_set_throw(EcmoraValue *out) {
    if (out != NULL) *out = ecmora_undefined();
}

static char *ecmora_copy_string(const char *input) {
    if (input == NULL) input = "";
    const size_t length = strlen(input);
    char *copy = (char *)malloc(length + 1);
    if (copy == NULL) abort();
    memcpy(copy, input, length + 1);
    return copy;
}

static char *ecmora_value_to_string(EcmoraValue value) {
    char buffer[96];
    switch (value.tag) {
        case ECMORA_UNDEFINED:
            return ecmora_copy_string("undefined");
        case ECMORA_NULL:
            return ecmora_copy_string("null");
        case ECMORA_BOOL:
            return ecmora_copy_string(value.payload == 0 ? "false" : "true");
        case ECMORA_NUMBER: {
            const double number = ecmora_number_value(value);
            if (isnan(number)) return ecmora_copy_string("NaN");
            if (isinf(number)) {
                return ecmora_copy_string(number < 0 ? "-Infinity" : "Infinity");
            }
            (void)snprintf(buffer, sizeof(buffer), "%.15g", number);
            return ecmora_copy_string(buffer);
        }
        case ECMORA_STRING:
            return ecmora_copy_string(
                value.payload == 0
                    ? ""
                    : (const char *)(uintptr_t)value.payload
            );
        case ECMORA_CALLABLE:
            return ecmora_copy_string("function () { [native code] }");
        case ECMORA_OBJECT:
            return ecmora_copy_string("[object Object]");
        case ECMORA_PROMISE:
            return ecmora_copy_string("[object Promise]");
        default:
            return ecmora_copy_string("undefined");
    }
}

static bool ecmora_primitive_numeric(EcmoraValue value) {
    return value.tag <= ECMORA_STRING;
}

static int32_t ecmora_to_int32(double input) {
    if (!isfinite(input) || input == 0.0) return 0;
    double integer = trunc(input);
    double modulo = fmod(integer, 4294967296.0);
    if (modulo < 0.0) modulo += 4294967296.0;
    if (modulo >= 2147483648.0) modulo -= 4294967296.0;
    return (int32_t)modulo;
}

static uint32_t ecmora_to_uint32(double input) {
    return (uint32_t)ecmora_to_int32(input);
}

static bool ecmora_strict_equal(EcmoraValue left, EcmoraValue right) {
    if (left.tag != right.tag) return false;
    switch (left.tag) {
        case ECMORA_UNDEFINED:
        case ECMORA_NULL:
            return true;
        case ECMORA_NUMBER: {
            const double a = ecmora_number_value(left);
            const double b = ecmora_number_value(right);
            return !isnan(a) && !isnan(b) && a == b;
        }
        case ECMORA_BOOL:
        case ECMORA_STRING:
        case ECMORA_OBJECT:
        case ECMORA_CALLABLE:
        case ECMORA_PROMISE:
        case ECMORA_CELL:
            if (left.tag == ECMORA_STRING) {
                const char *a = left.payload == 0
                    ? ""
                    : (const char *)(uintptr_t)left.payload;
                const char *b = right.payload == 0
                    ? ""
                    : (const char *)(uintptr_t)right.payload;
                return strcmp(a, b) == 0;
            }
            return left.payload == right.payload;
        default:
            return false;
    }
}

static bool ecmora_loose_equal(EcmoraValue left, EcmoraValue right) {
    if (left.tag == right.tag) return ecmora_strict_equal(left, right);
    if ((left.tag == ECMORA_NULL && right.tag == ECMORA_UNDEFINED)
        || (left.tag == ECMORA_UNDEFINED && right.tag == ECMORA_NULL)) {
        return true;
    }
    if (ecmora_primitive_numeric(left) && ecmora_primitive_numeric(right)) {
        const double a = ecmora_primitive_to_number(left.tag, left.payload);
        const double b = ecmora_primitive_to_number(right.tag, right.payload);
        return !isnan(a) && !isnan(b) && a == b;
    }
    return false;
}

static void ecmora_builder_reserve(ArgvBuilder *builder, uint32_t needed) {
    if (needed <= builder->capacity) return;
    uint32_t capacity = builder->capacity == 0 ? 8 : builder->capacity;
    while (capacity < needed) {
        if (capacity > UINT32_MAX / 2u) abort();
        capacity *= 2u;
    }
    EcmoraValue *grown = (EcmoraValue *)realloc(
        builder->values,
        sizeof(EcmoraValue) * (size_t)capacity
    );
    if (grown == NULL) abort();
    builder->values = grown;
    builder->capacity = capacity;
}

static void *ecmora_global_this_object(void) {
    static void *global_object = NULL;
    if (global_object == NULL) global_object = ecmora_object_new();
    return global_object;
}

void *ecmora_closure_new_ex(
    void *code,
    uint32_t capture_count,
    const EcmoraValue *captures,
    uint32_t flags,
    const EcmoraValue *lexical_this
) {
    EcmoraCallable *callable =
        (EcmoraCallable *)calloc(1, sizeof(EcmoraCallable));
    if (callable == NULL) abort();
    callable->magic = ECMORA_CALLABLE_MAGIC;
    callable->kind = ECMORA_CALLABLE_NATIVE;
    callable->code = (EcmoraCode)code;
    callable->flags = flags;
    callable->capture_count = capture_count;
    callable->lexical_this =
        lexical_this == NULL ? ecmora_undefined() : *lexical_this;

    if (capture_count != 0) {
        callable->captures = (EcmoraValue *)malloc(
            sizeof(EcmoraValue) * (size_t)capture_count
        );
        if (callable->captures == NULL) abort();
        memcpy(
            callable->captures,
            captures,
            sizeof(EcmoraValue) * (size_t)capture_count
        );
    }

    if ((flags & ECMORA_CALLABLE_CONSTRUCTABLE) != 0) {
        callable->prototype = ecmora_object_new();
        EcmoraValue self = ecmora_pointer(ECMORA_CALLABLE, callable);
        ecmora_object_set_value(callable->prototype, "constructor", &self);
    }
    return callable;
}

void *ecmora_closure_new(
    void *code,
    uint32_t capture_count,
    EcmoraValue *captures
) {
    return ecmora_closure_new_ex(
        code,
        capture_count,
        captures,
        ECMORA_CALLABLE_CONSTRUCTABLE,
        NULL
    );
}

void ecmora_closure_capture(
    void *pointer,
    uint32_t index,
    EcmoraValue *out
) {
    if (out == NULL) return;
    EcmoraCallable *callable = (EcmoraCallable *)pointer;
    if (callable == NULL
        || callable->magic != ECMORA_CALLABLE_MAGIC
        || index >= callable->capture_count) {
        *out = ecmora_undefined();
        return;
    }
    *out = callable->captures[index];
}

void ecmora_current_this(EcmoraValue *out) {
    if (out == NULL) return;
    *out = ecmora_invocation_top == NULL
        ? ecmora_undefined()
        : ecmora_invocation_top->this_value;
}

void ecmora_current_new_target(EcmoraValue *out) {
    if (out == NULL) return;
    *out = ecmora_invocation_top == NULL
        ? ecmora_undefined()
        : ecmora_invocation_top->new_target;
}

void *ecmora_arguments_object(
    uint32_t argc,
    const EcmoraValue *argv
) {
    void *object = ecmora_object_new();
    for (uint32_t index = 0; index < argc; ++index) {
        ecmora_object_set_index(object, index, &argv[index]);
    }
    return object;
}

void *ecmora_rest_array(
    uint32_t argc,
    const EcmoraValue *argv,
    uint32_t start
) {
    void *array = ecmora_object_new();
    uint32_t output = 0;
    for (uint32_t index = start; index < argc; ++index) {
        ecmora_object_set_index(array, output++, &argv[index]);
    }
    return array;
}

void ecmora_argv_builder_init(void **out) {
    if (out == NULL) return;
    ArgvBuilder *builder = (ArgvBuilder *)calloc(1, sizeof(ArgvBuilder));
    if (builder == NULL) abort();
    *out = builder;
}

void ecmora_argv_builder_push(
    void *pointer,
    const EcmoraValue *value
) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    if (builder == NULL || value == NULL) abort();
    ecmora_builder_reserve(builder, builder->length + 1u);
    builder->values[builder->length++] = *value;
}

uint8_t ecmora_argv_builder_spread(
    void *pointer,
    const EcmoraValue *iterable
) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    if (builder == NULL || iterable == NULL
        || iterable->tag != ECMORA_OBJECT
        || iterable->payload == 0) {
        return 1;
    }
    void *object = (void *)(uintptr_t)iterable->payload;
    const uint32_t length = ecmora_object_length(object);
    ecmora_builder_reserve(builder, builder->length + length);
    for (uint32_t index = 0; index < length; ++index) {
        EcmoraValue value = ecmora_undefined();
        (void)ecmora_object_get_index(object, index, &value);
        builder->values[builder->length++] = value;
    }
    return 0;
}

uint32_t ecmora_argv_builder_len(void *pointer) {
    const ArgvBuilder *builder = (const ArgvBuilder *)pointer;
    return builder == NULL ? 0u : builder->length;
}

const EcmoraValue *ecmora_argv_builder_data(void *pointer) {
    const ArgvBuilder *builder = (const ArgvBuilder *)pointer;
    return builder == NULL ? NULL : builder->values;
}

void ecmora_argv_builder_destroy(void *pointer) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    if (builder == NULL) return;
    free(builder->values);
    free(builder);
}

static uint8_t ecmora_dispatch_native(
    EcmoraCallable *callable,
    EcmoraValue this_value,
    EcmoraValue new_target,
    bool constructing,
    uint32_t argc,
    const EcmoraValue *argv,
    EcmoraValue *out
) {
    if (callable->code == NULL || (argc != 0 && argv == NULL)) {
        ecmora_set_throw(out);
        return 1;
    }

    if ((callable->flags & ECMORA_CALLABLE_LEXICAL_THIS) != 0) {
        this_value = callable->lexical_this;
    } else if ((callable->flags & ECMORA_CALLABLE_STRICT) == 0
               && (this_value.tag == ECMORA_UNDEFINED
                   || this_value.tag == ECMORA_NULL)) {
        this_value = ecmora_pointer(
            ECMORA_OBJECT,
            ecmora_global_this_object()
        );
    }

    InvocationFrame frame = {
        .this_value = this_value,
        .new_target = new_target,
        .callable = callable,
        .constructing = constructing,
        .previous = ecmora_invocation_top,
    };
    ecmora_invocation_top = &frame;
    const uint8_t status = callable->code(
        callable,
        argc,
        (EcmoraValue *)argv,
        out
    );
    ecmora_invocation_top = frame.previous;
    return status;
}

uint8_t ecmora_callable_dispatch(
    const EcmoraValue *callee_value,
    const EcmoraValue *this_value,
    const EcmoraValue *new_target,
    bool constructing,
    uint32_t argc,
    const EcmoraValue *argv,
    EcmoraValue *out
) {
    if (out != NULL) *out = ecmora_undefined();
    if (callee_value == NULL) return 1;
    EcmoraCallable *callable = ecmora_as_callable(*callee_value);
    if (callable == NULL) return 1;

    EcmoraValue receiver =
        this_value == NULL ? ecmora_undefined() : *this_value;
    EcmoraValue target =
        new_target == NULL ? ecmora_undefined() : *new_target;

    if (callable->kind == ECMORA_CALLABLE_BOUND) {
        ArgvBuilder builder = {0};
        ecmora_builder_reserve(
            &builder,
            callable->bound_argc + argc
        );
        for (uint32_t index = 0; index < callable->bound_argc; ++index) {
            builder.values[builder.length++] = callable->bound_argv[index];
        }
        for (uint32_t index = 0; index < argc; ++index) {
            builder.values[builder.length++] = argv[index];
        }

        const EcmoraValue effective_this =
            constructing ? receiver : callable->bound_this;
        if (constructing && target.tag == ECMORA_CALLABLE
            && target.payload == callee_value->payload) {
            target = callable->target;
        }
        const uint8_t status = ecmora_callable_dispatch(
            &callable->target,
            &effective_this,
            &target,
            constructing,
            builder.length,
            builder.values,
            out
        );
        free(builder.values);
        return status;
    }

    return ecmora_dispatch_native(
        callable,
        receiver,
        target,
        constructing,
        argc,
        argv,
        out
    );
}

uint8_t ecmora_closure_call(
    void *pointer,
    uint32_t argc,
    EcmoraValue *argv,
    EcmoraValue *out
) {
    EcmoraValue callee = ecmora_pointer(ECMORA_CALLABLE, pointer);
    EcmoraValue receiver = ecmora_undefined();
    EcmoraValue new_target = ecmora_undefined();
    return ecmora_callable_dispatch(
        &callee,
        &receiver,
        &new_target,
        false,
        argc,
        argv,
        out
    );
}

uint8_t ecmora_callable_construct(
    const EcmoraValue *callee_value,
    uint32_t argc,
    const EcmoraValue *argv,
    EcmoraValue *out
) {
    if (out != NULL) *out = ecmora_undefined();
    if (callee_value == NULL) return 1;

    EcmoraCallable *callable = ecmora_as_callable(*callee_value);
    if (callable == NULL) return 1;

    EcmoraCallable *construct_target = callable;
    while (construct_target->kind == ECMORA_CALLABLE_BOUND) {
        construct_target = ecmora_as_callable(construct_target->target);
        if (construct_target == NULL) return 1;
    }
    if ((construct_target->flags & ECMORA_CALLABLE_CONSTRUCTABLE) == 0) {
        return 1;
    }

    void *object = ecmora_object_new_with_prototype(
        construct_target->prototype
    );
    EcmoraValue receiver = ecmora_pointer(ECMORA_OBJECT, object);
    EcmoraValue result = ecmora_undefined();
    const uint8_t status = ecmora_callable_dispatch(
        callee_value,
        &receiver,
        callee_value,
        true,
        argc,
        argv,
        &result
    );
    if (status != 0) {
        if (out != NULL) *out = result;
        return status;
    }

    if (out != NULL) {
        *out = ecmora_is_object_like(result) ? result : receiver;
    }
    return 0;
}

uint8_t ecmora_callable_bind_value(
    const EcmoraValue *target,
    const EcmoraValue *bound_this,
    uint32_t bound_argc,
    const EcmoraValue *bound_argv,
    EcmoraValue *out
) {
    if (out != NULL) *out = ecmora_undefined();
    if (target == NULL || ecmora_as_callable(*target) == NULL) return 1;

    EcmoraCallable *bound =
        (EcmoraCallable *)calloc(1, sizeof(EcmoraCallable));
    if (bound == NULL) abort();
    bound->magic = ECMORA_CALLABLE_MAGIC;
    bound->kind = ECMORA_CALLABLE_BOUND;
    bound->target = *target;
    bound->bound_this =
        bound_this == NULL ? ecmora_undefined() : *bound_this;
    bound->bound_argc = bound_argc;
    if (bound_argc != 0) {
        bound->bound_argv = (EcmoraValue *)malloc(
            sizeof(EcmoraValue) * (size_t)bound_argc
        );
        if (bound->bound_argv == NULL) abort();
        memcpy(
            bound->bound_argv,
            bound_argv,
            sizeof(EcmoraValue) * (size_t)bound_argc
        );
    }
    if (out != NULL) {
        *out = ecmora_pointer(ECMORA_CALLABLE, bound);
    }
    return 0;
}

uint8_t ecmora_dynamic_get(
    const EcmoraValue *object,
    const char *key,
    EcmoraValue *out
) {
    if (out != NULL) *out = ecmora_undefined();
    if (object == NULL || key == NULL) return 1;

    if (object->tag == ECMORA_OBJECT && object->payload != 0) {
        (void)ecmora_object_get_value(
            (void *)(uintptr_t)object->payload,
            key,
            out
        );
        return 0;
    }

    if (object->tag == ECMORA_CALLABLE && object->payload != 0) {
        EcmoraCallable *callable = ecmora_as_callable(*object);
        if (callable == NULL) return 1;
        if (strcmp(key, "prototype") == 0) {
            if (out != NULL) {
                *out = callable->prototype == NULL
                    ? ecmora_undefined()
                    : ecmora_pointer(ECMORA_OBJECT, callable->prototype);
            }
            return 0;
        }
    }

    if (object->tag == ECMORA_STRING && strcmp(key, "length") == 0) {
        const char *text = object->payload == 0
            ? ""
            : (const char *)(uintptr_t)object->payload;
        if (out != NULL) *out = ecmora_number((double)strlen(text));
        return 0;
    }

    return 1;
}

uint8_t ecmora_dynamic_set(
    const EcmoraValue *object,
    const char *key,
    const EcmoraValue *value,
    EcmoraValue *error_out
) {
    ecmora_set_throw(error_out);
    if (object == NULL || key == NULL || value == NULL) return 1;

    if (object->tag == ECMORA_OBJECT && object->payload != 0) {
        ecmora_object_set_value(
            (void *)(uintptr_t)object->payload,
            key,
            value
        );
        return 0;
    }

    if (object->tag == ECMORA_CALLABLE
        && object->payload != 0
        && strcmp(key, "prototype") == 0
        && (value->tag == ECMORA_OBJECT || value->tag == ECMORA_NULL)) {
        EcmoraCallable *callable = ecmora_as_callable(*object);
        if (callable == NULL) return 1;
        callable->prototype = value->tag == ECMORA_NULL
            ? NULL
            : (void *)(uintptr_t)value->payload;
        return 0;
    }

    return 1;
}

uint8_t ecmora_dynamic_delete(
    const EcmoraValue *object,
    const char *key,
    EcmoraValue *out
) {
    if (out != NULL) *out = ecmora_bool(false);
    if (object == NULL || key == NULL) return 1;
    if (object->tag == ECMORA_OBJECT && object->payload != 0) {
        if (out != NULL) {
            *out = ecmora_bool(ecmora_object_delete(
                (void *)(uintptr_t)object->payload,
                key
            ));
        }
        return 0;
    }
    return 1;
}

void ecmora_array_push(
    void *array,
    const EcmoraValue *value
) {
    if (array == NULL || value == NULL) return;
    const uint32_t index = ecmora_object_length(array);
    ecmora_object_set_index(array, index, value);
}

uint8_t ecmora_array_spread(
    void *array,
    const EcmoraValue *iterable,
    EcmoraValue *error_out
) {
    ecmora_set_throw(error_out);
    if (array == NULL || iterable == NULL
        || iterable->tag != ECMORA_OBJECT
        || iterable->payload == 0) {
        return 1;
    }
    void *source = (void *)(uintptr_t)iterable->payload;
    const uint32_t length = ecmora_object_length(source);
    for (uint32_t index = 0; index < length; ++index) {
        EcmoraValue value = ecmora_undefined();
        (void)ecmora_object_get_index(source, index, &value);
        ecmora_array_push(array, &value);
    }
    return 0;
}

uint8_t ecmora_dynamic_unary(
    uint8_t operation,
    const EcmoraValue *operand,
    EcmoraValue *out
) {
    if (out != NULL) *out = ecmora_undefined();
    if (operand == NULL) return 1;

    switch (operation) {
        case 0: /* + */
            if (!ecmora_primitive_numeric(*operand)) return 1;
            if (out != NULL) {
                *out = ecmora_number(ecmora_primitive_to_number(
                    operand->tag,
                    operand->payload
                ));
            }
            return 0;
        case 1: /* - */
            if (!ecmora_primitive_numeric(*operand)) return 1;
            if (out != NULL) {
                *out = ecmora_number(-ecmora_primitive_to_number(
                    operand->tag,
                    operand->payload
                ));
            }
            return 0;
        case 2: { /* ! */
            bool truthy = true;
            if (operand->tag == ECMORA_UNDEFINED
                || operand->tag == ECMORA_NULL) {
                truthy = false;
            } else if (operand->tag == ECMORA_BOOL) {
                truthy = operand->payload != 0;
            } else if (operand->tag == ECMORA_NUMBER) {
                const double number = ecmora_number_value(*operand);
                truthy = number != 0.0 && !isnan(number);
            } else if (operand->tag == ECMORA_STRING) {
                truthy = operand->payload != 0
                    && ((const char *)(uintptr_t)operand->payload)[0] != '\0';
            }
            if (out != NULL) *out = ecmora_bool(!truthy);
            return 0;
        }
        case 3: /* ~ */
            if (!ecmora_primitive_numeric(*operand)) return 1;
            if (out != NULL) {
                *out = ecmora_number((double)~ecmora_to_int32(
                    ecmora_primitive_to_number(
                        operand->tag,
                        operand->payload
                    )
                ));
            }
            return 0;
        case 4: { /* typeof */
            const char *text = "undefined";
            switch (operand->tag) {
                case ECMORA_UNDEFINED: text = "undefined"; break;
                case ECMORA_NULL: text = "object"; break;
                case ECMORA_NUMBER: text = "number"; break;
                case ECMORA_BOOL: text = "boolean"; break;
                case ECMORA_STRING: text = "string"; break;
                case ECMORA_CALLABLE: text = "function"; break;
                default: text = "object"; break;
            }
            if (out != NULL) {
                *out = ecmora_pointer(ECMORA_STRING, (void *)text);
            }
            return 0;
        }
        case 5: /* void */
            if (out != NULL) *out = ecmora_undefined();
            return 0;
        default:
            return 1;
    }
}

uint8_t ecmora_dynamic_binary(
    uint8_t operation,
    const EcmoraValue *left,
    const EcmoraValue *right,
    EcmoraValue *out
) {
    if (out != NULL) *out = ecmora_undefined();
    if (left == NULL || right == NULL) return 1;

    if (operation == 8 || operation == 9) {
        bool equal = ecmora_strict_equal(*left, *right);
        if (operation == 9) equal = !equal;
        if (out != NULL) *out = ecmora_bool(equal);
        return 0;
    }
    if (operation == 6 || operation == 7) {
        bool equal = ecmora_loose_equal(*left, *right);
        if (operation == 7) equal = !equal;
        if (out != NULL) *out = ecmora_bool(equal);
        return 0;
    }

    if (operation == 20) { /* in */
        if (right->tag != ECMORA_OBJECT || right->payload == 0) return 1;
        char *key = ecmora_value_to_string(*left);
        EcmoraValue ignored = ecmora_undefined();
        const bool exists = ecmora_object_get_value(
            (void *)(uintptr_t)right->payload,
            key,
            &ignored
        );
        free(key);
        if (out != NULL) *out = ecmora_bool(exists);
        return 0;
    }

    if (operation == 21) { /* instanceof */
        EcmoraCallable *callable = ecmora_as_callable(*right);
        if (callable == NULL || callable->prototype == NULL
            || left->tag != ECMORA_OBJECT || left->payload == 0) {
            if (callable == NULL) return 1;
            if (out != NULL) *out = ecmora_bool(false);
            return 0;
        }
        void *cursor = ecmora_object_get_prototype(
            (void *)(uintptr_t)left->payload
        );
        bool matches = false;
        while (cursor != NULL) {
            if (cursor == callable->prototype) {
                matches = true;
                break;
            }
            cursor = ecmora_object_get_prototype(cursor);
        }
        if (out != NULL) *out = ecmora_bool(matches);
        return 0;
    }

    if (operation == 0
        && (left->tag == ECMORA_STRING || right->tag == ECMORA_STRING)) {
        char *a = ecmora_value_to_string(*left);
        char *b = ecmora_value_to_string(*right);
        const size_t a_length = strlen(a);
        const size_t b_length = strlen(b);
        char *joined = (char *)malloc(a_length + b_length + 1);
        if (joined == NULL) abort();
        memcpy(joined, a, a_length);
        memcpy(joined + a_length, b, b_length + 1);
        free(a);
        free(b);
        if (out != NULL) *out = ecmora_pointer(ECMORA_STRING, joined);
        return 0;
    }

    if ((operation >= 10 && operation <= 13)
        && left->tag == ECMORA_STRING
        && right->tag == ECMORA_STRING) {
        const char *a = left->payload == 0
            ? ""
            : (const char *)(uintptr_t)left->payload;
        const char *b = right->payload == 0
            ? ""
            : (const char *)(uintptr_t)right->payload;
        const int order = strcmp(a, b);
        bool result = false;
        switch (operation) {
            case 10: result = order < 0; break;
            case 11: result = order <= 0; break;
            case 12: result = order > 0; break;
            case 13: result = order >= 0; break;
            default: break;
        }
        if (out != NULL) *out = ecmora_bool(result);
        return 0;
    }

    if (!ecmora_primitive_numeric(*left)
        || !ecmora_primitive_numeric(*right)) {
        return 1;
    }
    const double a = ecmora_primitive_to_number(left->tag, left->payload);
    const double b = ecmora_primitive_to_number(right->tag, right->payload);

    switch (operation) {
        case 0:
            if (out != NULL) *out = ecmora_number(a + b);
            return 0;
        case 1:
            if (out != NULL) *out = ecmora_number(a - b);
            return 0;
        case 2:
            if (out != NULL) *out = ecmora_number(a * b);
            return 0;
        case 3:
            if (out != NULL) *out = ecmora_number(a / b);
            return 0;
        case 4:
            if (out != NULL) *out = ecmora_number(fmod(a, b));
            return 0;
        case 5:
            if (out != NULL) *out = ecmora_number(pow(a, b));
            return 0;
        case 10:
            if (out != NULL) *out = ecmora_bool(a < b);
            return 0;
        case 11:
            if (out != NULL) *out = ecmora_bool(a <= b);
            return 0;
        case 12:
            if (out != NULL) *out = ecmora_bool(a > b);
            return 0;
        case 13:
            if (out != NULL) *out = ecmora_bool(a >= b);
            return 0;
        case 14:
            if (out != NULL) {
                *out = ecmora_number((double)(
                    ecmora_to_int32(a) << (ecmora_to_uint32(b) & 31u)
                ));
            }
            return 0;
        case 15:
            if (out != NULL) {
                *out = ecmora_number((double)(
                    ecmora_to_int32(a) >> (ecmora_to_uint32(b) & 31u)
                ));
            }
            return 0;
        case 16:
            if (out != NULL) {
                *out = ecmora_number((double)(
                    ecmora_to_uint32(a) >> (ecmora_to_uint32(b) & 31u)
                ));
            }
            return 0;
        case 17:
            if (out != NULL) {
                *out = ecmora_number((double)(
                    ecmora_to_int32(a) | ecmora_to_int32(b)
                ));
            }
            return 0;
        case 18:
            if (out != NULL) {
                *out = ecmora_number((double)(
                    ecmora_to_int32(a) ^ ecmora_to_int32(b)
                ));
            }
            return 0;
        case 19:
            if (out != NULL) {
                *out = ecmora_number((double)(
                    ecmora_to_int32(a) & ecmora_to_int32(b)
                ));
            }
            return 0;
        default:
            return 1;
    }
}
