#ifndef ECMORA_FRAME_ABI_H
#define ECMORA_FRAME_ABI_H

#include <stdint.h>
#include "runtime_value.h"

/* ECMORA_SPLIT_RUNTIME_V11: argv/frame helpers only. */
void ecmora_argument_get(
    uint32_t argc,
    const EcmoraValue *argv,
    uint32_t index,
    EcmoraValue *out
);
EcmoraValue *ecmora_tail_argv_reserve(uint32_t count);

#endif
