#include "promise_abi.h"
#include "callable_abi.h"

#include <stdint.h>
#include <stdlib.h>

/* ECMORA_SPLIT_RUNTIME_V11: Promise implementation moved verbatim from object_runtime.c. */
typedef struct EcmoraCallable EcmoraClosure;

typedef enum {
    ECMORA_PROMISE_PENDING = 0,
    ECMORA_PROMISE_FULFILLED = 1,
    ECMORA_PROMISE_REJECTED = 2
} EcmoraPromiseState;

typedef struct EcmoraPromise EcmoraPromise;
typedef struct EcmoraPromiseReaction EcmoraPromiseReaction;

struct EcmoraPromise {
    EcmoraPromiseState state;
    EcmoraValue result;
    EcmoraPromiseReaction *reactions_head;
    EcmoraPromiseReaction *reactions_tail;
};

struct EcmoraPromiseReaction {
    EcmoraClosure *on_fulfilled;
    EcmoraClosure *on_rejected;
    EcmoraPromise *next;
    EcmoraPromiseReaction *next_reaction;
};

typedef struct EcmoraPromiseJob {
    EcmoraPromiseState state;
    EcmoraValue argument;
    EcmoraClosure *handler;
    EcmoraPromise *next;
    struct EcmoraPromiseJob *next_job;
} EcmoraPromiseJob;

static EcmoraPromiseJob *microtask_head = NULL;
static EcmoraPromiseJob *microtask_tail = NULL;

static EcmoraValue ecmora_undefined_value(void) {
    return (EcmoraValue){ ECMORA_UNDEFINED, 0 };
}

static EcmoraPromise *ecmora_promise_allocate(void) {
    EcmoraPromise *promise = (EcmoraPromise *)calloc(1, sizeof(EcmoraPromise));
    if (promise == NULL) abort();
    promise->state = ECMORA_PROMISE_PENDING;
    promise->result = ecmora_undefined_value();
    return promise;
}

static void ecmora_enqueue_promise_job(
    EcmoraPromiseState state,
    EcmoraValue argument,
    EcmoraClosure *handler,
    EcmoraPromise *next
) {
    EcmoraPromiseJob *job = (EcmoraPromiseJob *)calloc(1, sizeof(EcmoraPromiseJob));
    if (job == NULL) abort();
    job->state = state;
    job->argument = argument;
    job->handler = handler;
    job->next = next;
    if (microtask_tail == NULL) {
        microtask_head = job;
    } else {
        microtask_tail->next_job = job;
    }
    microtask_tail = job;
}

static void ecmora_promise_append_reaction(
    EcmoraPromise *source,
    EcmoraClosure *on_fulfilled,
    EcmoraClosure *on_rejected,
    EcmoraPromise *next
) {
    EcmoraPromiseReaction *reaction =
        (EcmoraPromiseReaction *)calloc(1, sizeof(EcmoraPromiseReaction));
    if (reaction == NULL) abort();
    reaction->on_fulfilled = on_fulfilled;
    reaction->on_rejected = on_rejected;
    reaction->next = next;
    if (source->reactions_tail == NULL) {
        source->reactions_head = reaction;
    } else {
        source->reactions_tail->next_reaction = reaction;
    }
    source->reactions_tail = reaction;
}

static void ecmora_trigger_promise_reactions(EcmoraPromise *promise) {
    EcmoraPromiseReaction *reaction = promise->reactions_head;
    promise->reactions_head = NULL;
    promise->reactions_tail = NULL;
    while (reaction != NULL) {
        EcmoraPromiseReaction *next_reaction = reaction->next_reaction;
        EcmoraClosure *handler =
            promise->state == ECMORA_PROMISE_FULFILLED
                ? reaction->on_fulfilled
                : reaction->on_rejected;
        ecmora_enqueue_promise_job(
            promise->state,
            promise->result,
            handler,
            reaction->next
        );
        free(reaction);
        reaction = next_reaction;
    }
}

static void ecmora_reject_promise(EcmoraPromise *promise, EcmoraValue reason) {
    if (promise == NULL || promise->state != ECMORA_PROMISE_PENDING) return;
    promise->state = ECMORA_PROMISE_REJECTED;
    promise->result = reason;
    ecmora_trigger_promise_reactions(promise);
}

static void ecmora_fulfill_promise(EcmoraPromise *promise, EcmoraValue value) {
    if (promise == NULL || promise->state != ECMORA_PROMISE_PENDING) return;
    promise->state = ECMORA_PROMISE_FULFILLED;
    promise->result = value;
    ecmora_trigger_promise_reactions(promise);
}

static void ecmora_resolve_promise(EcmoraPromise *promise, EcmoraValue resolution) {
    if (promise == NULL || promise->state != ECMORA_PROMISE_PENDING) return;

    if (resolution.tag == ECMORA_PROMISE && resolution.payload != 0) {
        EcmoraPromise *source = (EcmoraPromise *)(uintptr_t)resolution.payload;
        if (source == promise) {
            /*
             * The full engine will materialize a TypeError object. Until the
             * Error object model exists, preserve rejection completion rather
             * than hanging or fulfilling with self.
             */
            ecmora_reject_promise(promise, ecmora_undefined_value());
            return;
        }
        if (source->state == ECMORA_PROMISE_PENDING) {
            /*
             * Null handlers implement the identity/thrower defaults. The
             * capability promise adopts whichever state source eventually has.
             */
            ecmora_promise_append_reaction(source, NULL, NULL, promise);
            return;
        }
        if (source->state == ECMORA_PROMISE_REJECTED) {
            ecmora_reject_promise(promise, source->result);
        } else {
            ecmora_fulfill_promise(promise, source->result);
        }
        return;
    }

    /*
     * Dynamically shaped object thenables are rejected by native analysis and
     * compiled through the compatibility runtime. Reaching this C fallback
     * therefore means the value is proven non-thenable or primitive.
     */
    ecmora_fulfill_promise(promise, resolution);
}

void *ecmora_promise_resolved(const EcmoraValue *value) {
    EcmoraPromise *promise = ecmora_promise_allocate();
    ecmora_resolve_promise(
        promise,
        value == NULL ? ecmora_undefined_value() : *value
    );
    return promise;
}

void *ecmora_promise_rejected(const EcmoraValue *reason) {
    EcmoraPromise *promise = ecmora_promise_allocate();
    ecmora_reject_promise(
        promise,
        reason == NULL ? ecmora_undefined_value() : *reason
    );
    return promise;
}

void *ecmora_promise_pending(void) {
    return ecmora_promise_allocate();
}

void ecmora_promise_settle(
    void *promise_pointer,
    bool rejected,
    const EcmoraValue *value
) {
    EcmoraPromise *promise = (EcmoraPromise *)promise_pointer;
    EcmoraValue settlement =
        value == NULL ? ecmora_undefined_value() : *value;
    if (rejected) {
        ecmora_reject_promise(promise, settlement);
    } else {
        ecmora_resolve_promise(promise, settlement);
    }
}

void *ecmora_promise_then(
    void *source_pointer,
    void *on_fulfilled_pointer,
    void *on_rejected_pointer
) {
    EcmoraPromise *source = (EcmoraPromise *)source_pointer;
    EcmoraPromise *next = ecmora_promise_allocate();
    if (source == NULL) {
        ecmora_reject_promise(next, ecmora_undefined_value());
        return next;
    }

    EcmoraClosure *on_fulfilled = (EcmoraClosure *)on_fulfilled_pointer;
    EcmoraClosure *on_rejected = (EcmoraClosure *)on_rejected_pointer;
    if (source->state == ECMORA_PROMISE_PENDING) {
        ecmora_promise_append_reaction(
            source,
            on_fulfilled,
            on_rejected,
            next
        );
    } else {
        EcmoraClosure *handler =
            source->state == ECMORA_PROMISE_FULFILLED
                ? on_fulfilled
                : on_rejected;
        ecmora_enqueue_promise_job(
            source->state,
            source->result,
            handler,
            next
        );
    }
    return next;
}

void ecmora_microtask_drain(void) {
    while (microtask_head != NULL) {
        EcmoraPromiseJob *job = microtask_head;
        microtask_head = job->next_job;
        if (microtask_head == NULL) microtask_tail = NULL;

        if (job->next != NULL) {
            if (job->handler == NULL) {
                if (job->state == ECMORA_PROMISE_REJECTED) {
                    ecmora_reject_promise(job->next, job->argument);
                } else {
                    ecmora_fulfill_promise(job->next, job->argument);
                }
            } else {
                EcmoraValue output = ecmora_undefined_value();
                EcmoraValue argument = job->argument;
                uint8_t completion =
                    ecmora_closure_call(job->handler, 1, &argument, &output);
                if (completion == 1) {
                    ecmora_reject_promise(job->next, output);
                } else {
                    ecmora_resolve_promise(job->next, output);
                }
            }
        }
        free(job);
    }
}
