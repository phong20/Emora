#ifndef ECMORA_CALLABLE_ABI_H
#define ECMORA_CALLABLE_ABI_H

#include <stdbool.h>
#include <stdint.h>

typedef struct {
    uint8_t tag;
    uint64_t payload;
} EcmoraValue;

typedef struct {
    EcmoraValue this_value;
    EcmoraValue new_target;
    bool constructing;
} EcmoraInvocationContext;

uint8_t ecmora_callable_dispatch(
    EcmoraValue callee,
    EcmoraValue this_value,
    EcmoraValue new_target,
    bool constructing,
    uint32_t argc,
    const EcmoraValue *argv,
    EcmoraValue *out
);

void *ecmora_callable_bind(
    EcmoraValue target,
    EcmoraValue bound_this,
    uint32_t bound_argc,
    const EcmoraValue *bound_argv
);

void ecmora_current_this(EcmoraValue *out);
void ecmora_current_new_target(EcmoraValue *out);
bool ecmora_current_is_constructing(void);

void *ecmora_arguments_object(uint32_t argc, const EcmoraValue *argv);
void *ecmora_rest_array(uint32_t argc, const EcmoraValue *argv, uint32_t start);

void ecmora_argv_builder_init(void **builder);
void ecmora_argv_builder_push(void *builder, EcmoraValue value);
uint8_t ecmora_argv_builder_spread(void *builder, EcmoraValue iterable);
uint32_t ecmora_argv_builder_len(void *builder);
const EcmoraValue *ecmora_argv_builder_data(void *builder);
void ecmora_argv_builder_destroy(void *builder);

#endif
