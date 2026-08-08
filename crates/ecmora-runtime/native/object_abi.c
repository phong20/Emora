#include "object_abi.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ECMORA_SPLIT_RUNTIME_V11: object implementation moved verbatim from object_runtime.c. */
typedef union {
    double number;
    bool boolean;
    void *pointer;
} EcmoraPayload;

typedef struct EcmoraProperty {
    char *key;
    EcmoraTag tag;
    EcmoraPayload payload;
    void *getter;
    void *setter;
    bool enumerable;
    bool configurable;
    bool writable;
    struct EcmoraProperty *next;
} EcmoraProperty;

typedef struct {
    EcmoraProperty *head;
    void *prototype;
} EcmoraObject;

static char *copy_string(const char *source) {
    size_t length = strlen(source) + 1;
    char *copy = (char *)malloc(length);
    if (copy != NULL) memcpy(copy, source, length);
    return copy;
}

static EcmoraProperty *find_property(EcmoraObject *object, const char *key) {
    if (object == NULL) return NULL;
    for (EcmoraProperty *property = object->head; property != NULL; property = property->next) {
        if (strcmp(property->key, key) == 0) return property;
    }
    if (object->prototype != NULL) {
        return find_property((EcmoraObject *)object->prototype, key);
    }
    return NULL;
}

static EcmoraProperty *find_own_property(EcmoraObject *object, const char *key) {
    if (object == NULL) return NULL;
    for (EcmoraProperty *property = object->head; property != NULL; property = property->next) {
        if (strcmp(property->key, key) == 0) return property;
    }
    return NULL;
}

static EcmoraProperty *get_or_insert(EcmoraObject *object, const char *key) {
    EcmoraProperty *property = find_own_property(object, key);
    if (property != NULL) return property;
    property = (EcmoraProperty *)calloc(1, sizeof(EcmoraProperty));
    if (property == NULL) abort();
    property->key = copy_string(key);
    if (property->key == NULL) abort();
    property->enumerable = true;
    property->configurable = true;
    property->writable = true;
    property->next = object->head;
    object->head = property;
    return property;
}

void ecmora_object_define_accessor(void *pointer, const char *key, void *getter,
                                   void *setter, bool enumerable, bool configurable) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->configurable &&
        (property->enumerable != enumerable || configurable ||
         (getter != NULL && property->getter != getter) ||
         (setter != NULL && property->setter != setter))) {
        return;
    }
    if (getter != NULL) property->getter = getter;
    if (setter != NULL) property->setter = setter;
    property->enumerable = enumerable;
    property->configurable = configurable;
    property->writable = false;
}

void *ecmora_object_new(void) {
    EcmoraObject *object = (EcmoraObject *)calloc(1, sizeof(EcmoraObject));
    if (object == NULL) abort();
    return object;
}

void *ecmora_object_new_with_prototype(void *prototype) {
    EcmoraObject *object = (EcmoraObject *)ecmora_object_new();
    object->prototype = prototype;
    return object;
}

void ecmora_object_set_prototype(void *pointer, void *prototype) {
    if (pointer == NULL) return;
    for (EcmoraObject *cursor = (EcmoraObject *)prototype; cursor != NULL;
         cursor = (EcmoraObject *)cursor->prototype) {
        if (cursor == (EcmoraObject *)pointer) return;
    }
    ((EcmoraObject *)pointer)->prototype = prototype;
}

void *ecmora_object_get_prototype(void *pointer) {
    return pointer == NULL ? NULL : ((EcmoraObject *)pointer)->prototype;
}


bool ecmora_object_get_value(
    void *pointer,
    const char *key,
    EcmoraValue *out
) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    if (out == NULL) return property != NULL;
    if (property == NULL) {
        *out = (EcmoraValue){ ECMORA_UNDEFINED, 0 };
        return false;
    }
    out->tag = (uint8_t)property->tag;
    switch (property->tag) {
        case ECMORA_NUMBER:
            memcpy(&out->payload, &property->payload.number, sizeof(double));
            break;
        case ECMORA_BOOL:
            out->payload = property->payload.boolean ? 1 : 0;
            break;
        case ECMORA_UNDEFINED:
        case ECMORA_NULL:
            out->payload = 0;
            break;
        default:
            out->payload = (uint64_t)(uintptr_t)property->payload.pointer;
            break;
    }
    return true;
}

void ecmora_object_set_value(
    void *pointer,
    const char *key,
    const EcmoraValue *value
) {
    if (pointer == NULL || value == NULL) return;
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = (EcmoraTag)value->tag;
    switch ((EcmoraTag)value->tag) {
        case ECMORA_NUMBER:
            memcpy(&property->payload.number, &value->payload, sizeof(double));
            break;
        case ECMORA_BOOL:
            property->payload.boolean = value->payload != 0;
            break;
        default:
            property->payload.pointer = (void *)(uintptr_t)value->payload;
            break;
    }
}

double ecmora_object_get_number(void *pointer, const char *key) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    return property == NULL ? 0.0 : property->payload.number;
}

void ecmora_object_set_number(void *pointer, const char *key, double value) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_NUMBER;
    property->payload.number = value;
}

bool ecmora_object_get_bool(void *pointer, const char *key) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    return property != NULL && property->payload.boolean;
}

void ecmora_object_set_bool(void *pointer, const char *key, bool value) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_BOOL;
    property->payload.boolean = value;
}

void *ecmora_object_get_string(void *pointer, const char *key) {
    EcmoraProperty *property = find_property((EcmoraObject *)pointer, key);
    return property == NULL ? NULL : property->payload.pointer;
}

void ecmora_object_set_string(void *pointer, const char *key, void *value) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_STRING;
    property->payload.pointer = value;
}

void ecmora_object_set_undefined(void *pointer, const char *key) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_UNDEFINED;
    property->payload.pointer = NULL;
}

void ecmora_object_set_null(void *pointer, const char *key) {
    EcmoraProperty *property = get_or_insert((EcmoraObject *)pointer, key);
    if (!property->writable) return;
    property->tag = ECMORA_NULL;
    property->payload.pointer = NULL;
}

bool ecmora_object_delete(void *pointer, const char *key) {
    EcmoraObject *object = (EcmoraObject *)pointer;
    EcmoraProperty **cursor = &object->head;
    while (*cursor != NULL) {
        EcmoraProperty *property = *cursor;
        if (strcmp(property->key, key) == 0) {
            if (!property->configurable) return false;
            *cursor = property->next;
            free(property->key);
            free(property);
            return true;
        }
        cursor = &property->next;
    }
    return true;
}

/* generic callable ABI indexed object/array hooks */
void ecmora_object_set_index(
    void *pointer,
    uint32_t index,
    const EcmoraValue *value
) {
    char key[32];
    (void)snprintf(key, sizeof(key), "%u", index);
    ecmora_object_set_value(pointer, key, value);

    EcmoraValue current = { ECMORA_UNDEFINED, 0 };
    (void)ecmora_object_get_value(pointer, "length", &current);
    uint32_t length = 0;
    if (current.tag == ECMORA_NUMBER) {
        double number = 0.0;
        memcpy(&number, &current.payload, sizeof(number));
        if (number > 0.0 && number < (double)UINT32_MAX) {
            length = (uint32_t)number;
        }
    }
    if (index >= length) {
        const double next = (double)index + 1.0;
        EcmoraValue updated = { ECMORA_NUMBER, 0 };
        memcpy(&updated.payload, &next, sizeof(next));
        ecmora_object_set_value(pointer, "length", &updated);
    }
}

uint32_t ecmora_object_length(void *pointer) {
    EcmoraValue value = { ECMORA_UNDEFINED, 0 };
    if (!ecmora_object_get_value(pointer, "length", &value)
        || value.tag != ECMORA_NUMBER) {
        return 0;
    }
    double length = 0.0;
    memcpy(&length, &value.payload, sizeof(length));
    if (!(length > 0.0)) return 0;
    if (length >= (double)UINT32_MAX) return UINT32_MAX;
    return (uint32_t)length;
}

bool ecmora_object_get_index(
    void *pointer,
    uint32_t index,
    EcmoraValue *out
) {
    char key[32];
    (void)snprintf(key, sizeof(key), "%u", index);
    return ecmora_object_get_value(pointer, key, out);
}
