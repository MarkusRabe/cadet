//
//  val_vector.c
//  cadet
//
//  Created by Markus Rabe on 17/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "val_vector.h"
#include "qcnf.h"
#include "log.h"
#include "stdbool.h"
#include "util.h"

#include <assert.h>

#define VECTOR_NOT_FOUND (unsigned)-1
#define INITIAL_SIZE 2
#define INCREASE_FACTOR 2

void val_vector_increase(val_vector* v) {
    v->size *= INCREASE_FACTOR;
    v->data = realloc(v->data, sizeof(char) * v->size);
}

// assumes it can write to the memory location
void val_vector_init_struct(val_vector* v, unsigned size) {
    assert(v);
    v->data = malloc(sizeof(char) * size);
    v->count = 0;
    v->size = INITIAL_SIZE;
}

val_vector* val_vector_init() {
    val_vector* v = malloc(sizeof(val_vector));
    val_vector_init_struct(v, INITIAL_SIZE);
    return v;
}

val_vector* val_vector_init_at_size(unsigned initial_size) {
    val_vector* v = malloc(sizeof(val_vector));
    val_vector_init_struct(v, initial_size);
    return v;
}

void val_vector_resize(val_vector* v, unsigned size) {
    assert(size >= v->count);
    v->size = size;
    v->data = realloc(v->data, size * sizeof(char));
}

void val_vector_reset(val_vector* v) {
    v->count = 0;
}

void val_vector_free(val_vector* v) {
    free(v->data);
    free(v);
}

unsigned val_vector_count(val_vector* v) {
    return v->count;
}

void val_vector_reduce_count(val_vector* v, unsigned j) {
    assert(j <= v->count);
    v->count = j;
}

int val_vector_get(val_vector* v, unsigned i) {
    assert (v->count > i);
    return v->data[i];
}

void val_vector_set(val_vector* v, unsigned i, int value) {
    assert (v->count > i);
    v->data[i] = (char) value;
}

void val_vector_add(val_vector* v, int value) {
    if (v->size == v->count) {
        V4("Warning: Resizing value vector. Pointers may be invalidated!\n");
        val_vector_increase(v);
    }
    v->data[v->count] = (char) value;
    v->count += 1;
}

//void val_vector_print(val_vector* v) {
//    V4("val_vector (%u,%u) ", v->count, v->size);
//    for (unsigned j = 0; j < v->count; j++) {
//        Var* var = &v->data[j];
//        V1(" %d", var->val_id);
//    }
//    V1("\n");
//}

void val_vector_remove_index(val_vector* v, unsigned i) {
    v->count = v->count - 1; // yes, before the loop
    for (; i < v->count; i++) {
        v->data[i] = v->data[i+1];
    }
}

void val_vector_sort(val_vector* v, int (*cmp)(const void*, const void*)) {
    qsort(v->data, v->count, sizeof(Var), cmp);
}

val_vector* val_vector_copy(val_vector* old) {
    val_vector* new = val_vector_init();
    for (unsigned i = 0; i < val_vector_count(old); i++) {
        val_vector_add(new, val_vector_get(old, i));
    }
    return new;
}

void val_vector_add_all(val_vector* this, val_vector* other) {
    for (unsigned i = 0; i < val_vector_count(other); i++) {
        val_vector_add(this, val_vector_get(other, i));
    }
}

void val_vector_remove_last_element(val_vector* v) {
    assert(v->count > 0);
    v->count = v->count - 1;
}

