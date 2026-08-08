#ifndef ECMORA_RECURSION_ABI_H
#define ECMORA_RECURSION_ABI_H

#include <stdint.h>

/* ECMORA_SPLIT_RUNTIME_V11: native recursion guard ABI only. */
void ecmora_recursion_enter(const char *function_name, uint32_t limit);
void ecmora_recursion_leave(void);

#endif
