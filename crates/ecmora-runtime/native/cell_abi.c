#include "cell_abi.h"

#include <stdlib.h>

/* ECMORA_SPLIT_RUNTIME_V11: cell implementation moved verbatim from object_runtime.c. */
void *ecmora_cell_new(const EcmoraValue *initial) {
    EcmoraValue *cell = (EcmoraValue *)malloc(sizeof(EcmoraValue));
    if (cell == NULL) abort();
    *cell = initial == NULL ? (EcmoraValue){ ECMORA_UNDEFINED, 0 } : *initial;
    return cell;
}

void ecmora_cell_get(void *pointer, EcmoraValue *out) {
    if (pointer == NULL) {
        if (out != NULL) *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return;
    }
    if (out != NULL) *out = *(EcmoraValue *)pointer;
}

void ecmora_cell_set(void *pointer, const EcmoraValue *value) {
    if (pointer != NULL && value != NULL) *(EcmoraValue *)pointer = *value;
}
