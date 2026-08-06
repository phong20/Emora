#include "callable_abi.h"

#include <stdlib.h>
#include <string.h>

#define ECMORA_UNDEFINED 0
#define ECMORA_OBJECT 5
#define ECMORA_CALLABLE 6
#define ECMORA_CALLABLE_MAGIC UINT64_C(0x45434d4f52414341)

typedef uint8_t (*EcmoraLegacyCode)(
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
    EcmoraLegacyCode code;
    uint32_t capture_count;
    EcmoraValue *captures;
    EcmoraValue target;
    EcmoraValue bound_this;
    uint32_t bound_argc;
    EcmoraValue *bound_argv;
} EcmoraCallable;

typedef struct InvocationFrame {
    EcmoraInvocationContext context;
    struct InvocationFrame *previous;
} InvocationFrame;

typedef struct {
    EcmoraValue *values;
    uint32_t len;
    uint32_t cap;
} ArgvBuilder;

#if defined(_MSC_VER)
__declspec(thread) static InvocationFrame *invocation_top = NULL;
#else
static _Thread_local InvocationFrame *invocation_top = NULL;
#endif

extern void *ecmora_object_new(void);
extern void ecmora_object_set_index(void *, uint32_t, const EcmoraValue *);
extern uint32_t ecmora_object_length(void *);
extern bool ecmora_object_get_index(void *, uint32_t, EcmoraValue *);

static EcmoraValue undefined_value(void) {
    EcmoraValue value = { ECMORA_UNDEFINED, 0 };
    return value;
}

static EcmoraCallable *as_callable(EcmoraValue value) {
    if (value.tag != ECMORA_CALLABLE || value.payload == 0) return NULL;
    EcmoraCallable *callable = (EcmoraCallable *)(uintptr_t)value.payload;
    return callable->magic == ECMORA_CALLABLE_MAGIC ? callable : NULL;
}

static void reserve(ArgvBuilder *builder, uint32_t needed) {
    if (needed <= builder->cap) return;
    uint32_t cap = builder->cap == 0 ? 8 : builder->cap;
    while (cap < needed) cap *= 2;
    EcmoraValue *grown = (EcmoraValue *)realloc(
        builder->values, sizeof(EcmoraValue) * (size_t)cap
    );
    if (grown == NULL) abort();
    builder->values = grown;
    builder->cap = cap;
}

void ecmora_current_this(EcmoraValue *out) {
    if (out != NULL) {
        *out = invocation_top == NULL
            ? undefined_value()
            : invocation_top->context.this_value;
    }
}

void ecmora_current_new_target(EcmoraValue *out) {
    if (out != NULL) {
        *out = invocation_top == NULL
            ? undefined_value()
            : invocation_top->context.new_target;
    }
}

bool ecmora_current_is_constructing(void) {
    return invocation_top != NULL && invocation_top->context.constructing;
}

void *ecmora_arguments_object(uint32_t argc, const EcmoraValue *argv) {
    void *object = ecmora_object_new();
    for (uint32_t index = 0; index < argc; ++index) {
        ecmora_object_set_index(object, index, &argv[index]);
    }
    return object;
}

void *ecmora_rest_array(uint32_t argc, const EcmoraValue *argv, uint32_t start) {
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

void ecmora_argv_builder_push(void *pointer, EcmoraValue value) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    if (builder == NULL) abort();
    reserve(builder, builder->len + 1);
    builder->values[builder->len++] = value;
}

uint8_t ecmora_argv_builder_spread(void *pointer, EcmoraValue iterable) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    if (builder == NULL || iterable.tag != ECMORA_OBJECT || iterable.payload == 0) {
        return 1;
    }
    void *object = (void *)(uintptr_t)iterable.payload;
    uint32_t length = ecmora_object_length(object);
    reserve(builder, builder->len + length);
    for (uint32_t index = 0; index < length; ++index) {
        EcmoraValue value = undefined_value();
        (void)ecmora_object_get_index(object, index, &value);
        builder->values[builder->len++] = value;
    }
    return 0;
}

uint32_t ecmora_argv_builder_len(void *pointer) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    return builder == NULL ? 0 : builder->len;
}

const EcmoraValue *ecmora_argv_builder_data(void *pointer) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    return builder == NULL ? NULL : builder->values;
}

void ecmora_argv_builder_destroy(void *pointer) {
    ArgvBuilder *builder = (ArgvBuilder *)pointer;
    if (builder == NULL) return;
    free(builder->values);
    free(builder);
}

void *ecmora_callable_bind(
    EcmoraValue target,
    EcmoraValue bound_this,
    uint32_t bound_argc,
    const EcmoraValue *bound_argv
) {
    if (as_callable(target) == NULL) return NULL;
    EcmoraCallable *bound = (EcmoraCallable *)calloc(1, sizeof(EcmoraCallable));
    if (bound == NULL) abort();
    bound->magic = ECMORA_CALLABLE_MAGIC;
    bound->kind = ECMORA_CALLABLE_BOUND;
    bound->target = target;
    bound->bound_this = bound_this;
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
    return bound;
}

uint8_t ecmora_callable_dispatch(
    EcmoraValue callee,
    EcmoraValue this_value,
    EcmoraValue new_target,
    bool constructing,
    uint32_t argc,
    const EcmoraValue *argv,
    EcmoraValue *out
) {
    if (out != NULL) *out = undefined_value();
    EcmoraCallable *callable = as_callable(callee);
    if (callable == NULL) return 1;

    if (callable->kind == ECMORA_CALLABLE_BOUND) {
        ArgvBuilder builder = {0};
        reserve(&builder, callable->bound_argc + argc);
        for (uint32_t i = 0; i < callable->bound_argc; ++i) {
            builder.values[builder.len++] = callable->bound_argv[i];
        }
        for (uint32_t i = 0; i < argc; ++i) {
            builder.values[builder.len++] = argv[i];
        }
        EcmoraValue effective_this = constructing ? this_value : callable->bound_this;
        uint8_t completion = ecmora_callable_dispatch(
            callable->target,
            effective_this,
            new_target,
            constructing,
            builder.len,
            builder.values,
            out
        );
        free(builder.values);
        return completion;
    }

    if (callable->code == NULL || (argc != 0 && argv == NULL)) return 1;
    InvocationFrame frame = {
        .context = {
            .this_value = this_value,
            .new_target = new_target,
            .constructing = constructing,
        },
        .previous = invocation_top,
    };
    invocation_top = &frame;
    uint8_t completion = callable->code(
        callable,
        argc,
        (EcmoraValue *)argv,
        out
    );
    invocation_top = frame.previous;
    return completion;
}
