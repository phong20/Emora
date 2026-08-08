#include "value_abi.h"
#include "runtime_value.h"

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ECMORA_SPLIT_RUNTIME_V11: value conversion implementation moved verbatim. */
static const char *ecmora_skip_space(const char *text) {
    while (*text == ' ' || *text == '\t' || *text == '\n' || *text == '\r'
           || *text == '\f' || *text == '\v') {
        text += 1;
    }
    return text;
}

static double ecmora_parse_primitive_number(const char *text) {
    if (text == NULL) return 0.0;
    text = ecmora_skip_space(text);
    size_t length = strlen(text);
    while (length != 0) {
        char tail = text[length - 1];
        if (tail == ' ' || tail == '\t' || tail == '\n' || tail == '\r'
            || tail == '\f' || tail == '\v') {
            length -= 1;
        } else {
            break;
        }
    }
    if (length == 0) return 0.0;

    char *copy = (char *)malloc(length + 1);
    if (copy == NULL) abort();
    memcpy(copy, text, length);
    copy[length] = '\0';

    if (strcmp(copy, "Infinity") == 0 || strcmp(copy, "+Infinity") == 0) {
        free(copy);
        return INFINITY;
    }
    if (strcmp(copy, "-Infinity") == 0) {
        free(copy);
        return -INFINITY;
    }

    const char *digits = copy;
    int radix = 10;
    if (length > 2 && copy[0] == '0') {
        if (copy[1] == 'x' || copy[1] == 'X') {
            radix = 16;
            digits += 2;
        } else if (copy[1] == 'o' || copy[1] == 'O') {
            radix = 8;
            digits += 2;
        } else if (copy[1] == 'b' || copy[1] == 'B') {
            radix = 2;
            digits += 2;
        }
    }

    double result;
    if (radix != 10) {
        if (*digits == '\0') {
            result = NAN;
        } else {
            result = 0.0;
            for (const char *cursor = digits; *cursor != '\0'; cursor += 1) {
                int digit;
                if (*cursor >= '0' && *cursor <= '9') {
                    digit = *cursor - '0';
                } else if (*cursor >= 'a' && *cursor <= 'f') {
                    digit = *cursor - 'a' + 10;
                } else if (*cursor >= 'A' && *cursor <= 'F') {
                    digit = *cursor - 'A' + 10;
                } else {
                    result = NAN;
                    break;
                }
                if (digit >= radix) {
                    result = NAN;
                    break;
                }
                result = result * radix + digit;
            }
        }
    } else {
        bool valid = true;
        for (const char *cursor = copy; *cursor != '\0'; cursor += 1) {
            if (!((*cursor >= '0' && *cursor <= '9')
                  || *cursor == '.'
                  || *cursor == 'e'
                  || *cursor == 'E'
                  || *cursor == '+'
                  || *cursor == '-')) {
                valid = false;
                break;
            }
        }
        char *end = NULL;
        result = valid ? strtod(copy, &end) : NAN;
        if (!valid || end == copy || *end != '\0') result = NAN;
    }
    free(copy);
    return result;
}

double ecmora_primitive_to_number(uint8_t tag, uint64_t payload) {
    switch (tag) {
        case ECMORA_UNDEFINED:
            return NAN;
        case ECMORA_NULL:
            return 0.0;
        case ECMORA_NUMBER: {
            double number;
            memcpy(&number, &payload, sizeof(number));
            return number;
        }
        case ECMORA_BOOL:
            return payload == 0 ? 0.0 : 1.0;
        case ECMORA_STRING:
            return ecmora_parse_primitive_number(
                payload == 0 ? "" : (const char *)(uintptr_t)payload
            );
        default:
            fputs(
                "Ecmora native ToNumber received object/BigInt-capable dynamic value\n",
                stderr
            );
            abort();
    }
}

bool ecmora_dynamic_to_bool(uint8_t tag, uint64_t payload) {
    if (tag == 0 || tag == 1) return false;
    if (tag == 3) return payload != 0;
    if (tag == 2) {
        double number;
        memcpy(&number, &payload, sizeof(number));
        return number != 0.0 && number == number;
    }
    if (tag == 4) return payload != 0;
    return true;
}
