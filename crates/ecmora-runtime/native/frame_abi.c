#include "frame_abi.h"

#include <stdlib.h>

/* ECMORA_SPLIT_RUNTIME_V11: frame implementation moved verbatim from object_runtime.c. */
void ecmora_argument_get(
    uint32_t argc,
    const EcmoraValue *argv,
    uint32_t index,
    EcmoraValue *out
) {
    if (out == NULL) return;
    if (argv == NULL || index >= argc) {
        *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return;
    }
    *out = argv[index];
}

#if defined(_MSC_VER)
__declspec(thread) static EcmoraValue *ecmora_tail_argv_buffer = NULL;
__declspec(thread) static uint32_t ecmora_tail_argv_capacity = 0;
#else
static _Thread_local EcmoraValue *ecmora_tail_argv_buffer = NULL;
static _Thread_local uint32_t ecmora_tail_argv_capacity = 0;
#endif

EcmoraValue *ecmora_tail_argv_reserve(uint32_t count) {
    if (count == 0) return NULL;
    if (count > ecmora_tail_argv_capacity) {
        EcmoraValue *grown = (EcmoraValue *)realloc(
            ecmora_tail_argv_buffer,
            sizeof(EcmoraValue) * (size_t)count
        );
        if (grown == NULL) abort();
        ecmora_tail_argv_buffer = grown;
        ecmora_tail_argv_capacity = count;
    }
    return ecmora_tail_argv_buffer;
}
