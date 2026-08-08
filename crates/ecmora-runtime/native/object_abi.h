#ifndef ECMORA_OBJECT_ABI_H
#define ECMORA_OBJECT_ABI_H

#include <stdbool.h>
#include <stdint.h>
#include "runtime_value.h"

/* ECMORA_SPLIT_RUNTIME_V11: dedicated heap-object ABI. */
void *ecmora_object_new(void);
void *ecmora_object_new_with_prototype(void *prototype);
void ecmora_object_set_prototype(void *object, void *prototype);
void *ecmora_object_get_prototype(void *object);

void ecmora_object_define_accessor(
    void *object,
    const char *key,
    void *getter,
    void *setter,
    bool enumerable,
    bool configurable
);

bool ecmora_object_get_value(void *object, const char *key, EcmoraValue *out);
void ecmora_object_set_value(
    void *object,
    const char *key,
    const EcmoraValue *value
);

double ecmora_object_get_number(void *object, const char *key);
void ecmora_object_set_number(void *object, const char *key, double value);
bool ecmora_object_get_bool(void *object, const char *key);
void ecmora_object_set_bool(void *object, const char *key, bool value);
void *ecmora_object_get_string(void *object, const char *key);
void ecmora_object_set_string(void *object, const char *key, void *value);
void ecmora_object_set_undefined(void *object, const char *key);
void ecmora_object_set_null(void *object, const char *key);
bool ecmora_object_delete(void *object, const char *key);

void ecmora_object_set_index(
    void *object,
    uint32_t index,
    const EcmoraValue *value
);
uint32_t ecmora_object_length(void *object);
bool ecmora_object_get_index(
    void *object,
    uint32_t index,
    EcmoraValue *out
);

#endif
