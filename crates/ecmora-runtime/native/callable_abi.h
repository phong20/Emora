#ifndef ECMORA_CALLABLE_ABI_H
#define ECMORA_CALLABLE_ABI_H

#include <stdbool.h>
#include <stdint.h>

typedef struct {
    uint8_t tag;
    uint64_t payload;
} EcmoraValue;

enum {
    ECMORA_CALLABLE_CONSTRUCTABLE = 1u << 0,
    ECMORA_CALLABLE_LEXICAL_THIS = 1u << 1,
    ECMORA_CALLABLE_STRICT = 1u << 2
};

void *ecmora_closure_new(
    void *code,
    uint32_t capture_count,
    EcmoraValue *captures
);

void *ecmora_closure_new_ex(
    void *code,
    uint32_t capture_count,
    const EcmoraValue *captures,
    uint32_t flags,
    const EcmoraValue *lexical_this
);

void ecmora_closure_capture(
    void *closure,
    uint32_t index,
    EcmoraValue *out
);

uint8_t ecmora_closure_call(
    void *closure,
    uint32_t argc,
    EcmoraValue *argv,
    EcmoraValue *out
);

void ecmora_current_this(EcmoraValue *out);
void ecmora_current_new_target(EcmoraValue *out);

void *ecmora_arguments_object(
    uint32_t argc,
    const EcmoraValue *argv
);

void *ecmora_rest_array(
    uint32_t argc,
    const EcmoraValue *argv,
    uint32_t start
);

void ecmora_argv_builder_init(void **builder);
void ecmora_argv_builder_push(
    void *builder,
    const EcmoraValue *value
);
uint8_t ecmora_argv_builder_spread(
    void *builder,
    const EcmoraValue *iterable
);
uint32_t ecmora_argv_builder_len(void *builder);
const EcmoraValue *ecmora_argv_builder_data(void *builder);
void ecmora_argv_builder_destroy(void *builder);

uint8_t ecmora_callable_dispatch(
    const EcmoraValue *callee,
    const EcmoraValue *this_value,
    const EcmoraValue *new_target,
    bool constructing,
    uint32_t argc,
    const EcmoraValue *argv,
    EcmoraValue *out
);

uint8_t ecmora_callable_construct(
    const EcmoraValue *callee,
    uint32_t argc,
    const EcmoraValue *argv,
    EcmoraValue *out
);

uint8_t ecmora_callable_bind_value(
    const EcmoraValue *target,
    const EcmoraValue *bound_this,
    uint32_t bound_argc,
    const EcmoraValue *bound_argv,
    EcmoraValue *out
);

uint8_t ecmora_dynamic_unary(
    uint8_t operation,
    const EcmoraValue *operand,
    EcmoraValue *out
);

uint8_t ecmora_dynamic_binary(
    uint8_t operation,
    const EcmoraValue *left,
    const EcmoraValue *right,
    EcmoraValue *out
);

uint8_t ecmora_dynamic_get(
    const EcmoraValue *object,
    const char *key,
    EcmoraValue *out
);

uint8_t ecmora_dynamic_set(
    const EcmoraValue *object,
    const char *key,
    const EcmoraValue *value,
    EcmoraValue *error_out
);

uint8_t ecmora_dynamic_delete(
    const EcmoraValue *object,
    const char *key,
    EcmoraValue *out
);

void ecmora_array_push(
    void *array,
    const EcmoraValue *value
);

uint8_t ecmora_array_spread(
    void *array,
    const EcmoraValue *iterable,
    EcmoraValue *error_out
);

#endif
