#ifndef ECMORA_VALUE_ABI_H
#define ECMORA_VALUE_ABI_H

#include <stdbool.h>
#include <stdint.h>

/* ECMORA_SPLIT_RUNTIME_V11: primitive conversion/truthiness ABI only. */
double ecmora_primitive_to_number(uint8_t tag, uint64_t payload);
bool ecmora_dynamic_to_bool(uint8_t tag, uint64_t payload);

#endif
