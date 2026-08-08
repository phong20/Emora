#ifndef ECMORA_PROMISE_ABI_H
#define ECMORA_PROMISE_ABI_H

#include <stdbool.h>
#include "runtime_value.h"

/* ECMORA_SPLIT_RUNTIME_V11: Promise/microtask ABI only. */
void *ecmora_promise_resolved(const EcmoraValue *value);
void *ecmora_promise_rejected(const EcmoraValue *reason);
void *ecmora_promise_pending(void);
void ecmora_promise_settle(
    void *promise,
    bool rejected,
    const EcmoraValue *value
);
void *ecmora_promise_then(
    void *source,
    void *on_fulfilled,
    void *on_rejected
);
void ecmora_microtask_drain(void);

#endif
