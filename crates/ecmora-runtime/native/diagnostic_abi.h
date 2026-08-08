#ifndef ECMORA_DIAGNOSTIC_ABI_H
#define ECMORA_DIAGNOSTIC_ABI_H

#include <stdint.h>

/* ECMORA_SPLIT_RUNTIME_V11: native display/uncaught-completion ABI only. */
void ecmora_print_dynamic(uint8_t tag, uint64_t payload);
void ecmora_throw_uncaught(uint8_t tag, uint64_t payload);

#endif
