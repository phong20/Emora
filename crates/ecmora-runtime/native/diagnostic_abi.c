#include "diagnostic_abi.h"
#include "runtime_value.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ECMORA_SPLIT_RUNTIME_V11: diagnostic implementation moved verbatim. */
static void ecmora_fprint_dynamic(FILE *stream, uint8_t tag, uint64_t payload) {
    switch (tag) {
        case ECMORA_UNDEFINED: fputs("undefined", stream); break;
        case ECMORA_NULL: fputs("null", stream); break;
        case ECMORA_NUMBER: {
            double number;
            memcpy(&number, &payload, sizeof(number));
            fprintf(stream, "%.15g", number);
            break;
        }
        case ECMORA_BOOL: fputs(payload ? "true" : "false", stream); break;
        case ECMORA_STRING:
            fputs(payload ? (const char *)((uintptr_t)payload) : "", stream);
            break;
        case ECMORA_OBJECT: fputs("[object Object]", stream); break;
        case ECMORA_CALLABLE: fputs("function () { [native code] }", stream); break;
        case ECMORA_PROMISE: fputs("[object Promise]", stream); break;
        case ECMORA_CELL: fputs("[object Cell]", stream); break;
        default: fputs("undefined", stream); break;
    }
}

void ecmora_print_dynamic(uint8_t tag, uint64_t payload) {
    ecmora_fprint_dynamic(stdout, tag, payload);
}

void ecmora_throw_uncaught(uint8_t tag, uint64_t payload) {
    fputs("Uncaught ", stderr);
    ecmora_fprint_dynamic(stderr, tag, payload);
    fputc('\n', stderr);
    fflush(stderr);
    abort();
}
