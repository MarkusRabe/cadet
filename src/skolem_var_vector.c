//
//  skolem_var_vector.c
//  cadet
//
//  Created by Markus Rabe on 20/11/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "skolem_var_vector.h"
#include "skolem.h"
#include "log.h"
#include "stdbool.h"
#include "util.h"

#include <assert.h>

#define VECTOR_NOT_FOUND (unsigned)-1
#define INITIAL_SIZE 2
#define INCREASE_FACTOR 2

void skolem_var_vector_increase(skolem_var_vector* v) {
    v->size *= INCREASE_FACTOR;
    v->data = realloc(v->data, sizeof(skolem_var) * v->size);
    //    skolem_var* newdata = malloc(sizeof(skolem_var) * v->size);
    //    for (unsigned i = 0; i < v->count; i++) {
    //        newdata[i] = v->data[i];
    //    }
    //    free(v->data);
    //    v->data = newdata;
}

skolem_var_vector* skolem_var_vector_init() {
    skolem_var_vector* v = malloc(sizeof(skolem_var_vector));
    skolem_var_vector_init_struct(v, (unsigned) INITIAL_SIZE);
    return v;
}

skolem_var_vector* skolem_var_vector_init_with_size(unsigned init_size) {
    skolem_var_vector* v = malloc(sizeof(skolem_var_vector));
    skolem_var_vector_init_struct(v, init_size);
    return v;
}

void skolem_var_vector_init_struct(skolem_var_vector* v, unsigned init_size) {
    assert(v);
    assert(init_size > 0);
    v->data = malloc(sizeof(skolem_var) * init_size);
    v->count = 0;
    v->size = init_size;
}

void skolem_var_vector_reset(skolem_var_vector* v) {
    v->count = 0;
}

void skolem_var_vector_free(skolem_var_vector* v) {
    free(v->data);
    free(v);
}

unsigned skolem_var_vector_count(skolem_var_vector* v) {
    return v->count;
}

void skolem_var_vector_reduce_count(skolem_var_vector* v, unsigned j) {
    assert(j <= v->count);
    v->count = j;
}

skolem_var* skolem_var_vector_get(skolem_var_vector* v, unsigned i) {
    assert (v->count > i);
    return &v->data[i];
}

void skolem_var_vector_set(skolem_var_vector* v, unsigned i, skolem_var value) {
    assert (v->count > i);
    v->data[i] = value;
}

void skolem_var_vector_add(skolem_var_vector* v, skolem_var value) {
    if (v->size == v->count) {
        skolem_var_vector_increase(v);
    }
    v->data[v->count] = value;
    v->count += 1;
}

void skolem_var_vector_print(skolem_var_vector* v) {
    V4("skolem_var_vector (%u,%u) ", v->count, v->size);
    for (unsigned j = 0; j < v->count; j++) {
        skolem_var sv = v->data[j];
        V1(" (%d %d %d%d%d)", sv.pos_lit, sv.neg_lit, sv.pure_pos, sv.pure_neg, sv.deterministic);
    }
    V1("\n");
}

void skolem_var_vector_remove_index(skolem_var_vector* v, unsigned i) {
    v->count = v->count - 1; // yes, before the loop
    for (; i < v->count; i++) {
        v->data[i] = v->data[i+1];
    }
}

void skolem_var_vector_sort(skolem_var_vector* v, int (*cmp)(const void*, const void*)) {
    qsort(v->data, v->count, sizeof(skolem_var), cmp);
}

skolem_var_vector* skolem_var_vector_copy(skolem_var_vector* old) {
    skolem_var_vector* new = skolem_var_vector_init();
    for (unsigned i = 0; i < skolem_var_vector_count(old); i++) {
        skolem_var_vector_add(new, *skolem_var_vector_get(old, i));
    }
    return new;
}

void skolem_var_vector_add_all(skolem_var_vector* this, skolem_var_vector* other) {
    for (unsigned i = 0; i < skolem_var_vector_count(other); i++) {
        skolem_var_vector_add(this, *skolem_var_vector_get(other, i));
    }
}

