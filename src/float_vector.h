//
//  float_vector.h
//  cadet
//
//  Created by Markus Rabe on 13.09.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef float_vector_h
#define float_vector_h

#include <stdlib.h>
#include <stdbool.h>

typedef struct {
    float*   data;
    unsigned size;
    unsigned count;
} float_vector;

float_vector* float_vector_init();
void float_vector_init_struct(float_vector*);
unsigned float_vector_count(float_vector* v);
void float_vector_reduce_count(float_vector* v, unsigned j);
void float_vector_add(float_vector* v, float value);
void float_vector_add_sorted(float_vector* v, float value);
void float_vector_set(float_vector* v, unsigned i, float value);
float float_vector_get(float_vector* v, unsigned i);
float float_vector_pop(float_vector* v);
unsigned float_vector_find(float_vector* v, float value);
unsigned float_vector_find_sorted(float_vector* v, float value);
bool float_vector_contains_sorted(float_vector* v, float value);
bool float_vector_contains(float_vector* v, float value);
float* float_vector_get_data(float_vector* v);
void float_vector_free(float_vector* v);
void float_vector_print(float_vector* v);
void float_vector_reset(float_vector* v);
bool float_vector_remove(float_vector* v, float value);
void float_vector_remove_index(float_vector* v, unsigned index);
bool float_vector_is_strictly_sorted(float_vector* v);
void float_vector_sort(float_vector* v, int (*compar)(const void *, const void*));
void float_vector_remove_duplicates(float_vector*);
float_vector* float_vector_copy(float_vector*);
bool float_vector_includes_sorted(float_vector*,float_vector*); // compare by subset relation
void float_vector_add_all_sorted(float_vector* add_to, float_vector* to_add); // Adds the elements of the second to the first, sorts in the end
void float_vector_add_all(float_vector* add_to, float_vector* to_add); // Adds the elements of the second to the first

#endif /* float_vector_h */
