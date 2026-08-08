#ifndef ECMORA_CELL_ABI_H
#define ECMORA_CELL_ABI_H

#include "runtime_value.h"

/* ECMORA_SPLIT_RUNTIME_V11: captured-cell ABI only. */
void *ecmora_cell_new(const EcmoraValue *initial);
void ecmora_cell_get(void *cell, EcmoraValue *out);
void ecmora_cell_set(void *cell, const EcmoraValue *value);

#endif
