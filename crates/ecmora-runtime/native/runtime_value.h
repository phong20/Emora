#ifndef ECMORA_RUNTIME_VALUE_H
#define ECMORA_RUNTIME_VALUE_H

#include <stdint.h>

/* ECMORA_SPLIT_RUNTIME_V11: one shared tagged-value ABI; no runtime implementation here. */
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

typedef struct {
    uint8_t tag;
    uint64_t payload;
} EcmoraValue;

#endif
