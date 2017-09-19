//
//  int_vector.h
//  cadet
//
//  Created by Markus Rabe on 20/11/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef int_vector_h
#define int_vector_h

#include <stdlib.h>
#include <stdbool.h>

typedef struct {
    int*   data;
    unsigned size;
    unsigned count;
} int_vector;

int_vector* int_vector_init();
void int_vector_init_struct(int_vector*);
unsigned int_vector_count(int_vector* v);
void int_vector_reduce_count(int_vector* v, unsigned j);
void int_vector_add(int_vector* v, int value);
void int_vector_add_sorted(int_vector* v, int value);
void int_vector_set(int_vector* v, unsigned i, int value);
int int_vector_get(int_vector* v, unsigned i);
int int_vector_pop(int_vector* v);
unsigned int_vector_find(int_vector* v, int value);
unsigned int_vector_find_sorted(int_vector* v, int value);
bool int_vector_contains_sorted(int_vector* v, int value);
bool int_vector_contains(int_vector* v, int value);
int* int_vector_get_data(int_vector* v);
void int_vector_free(int_vector* v);
void int_vector_print(int_vector* v);
void int_vector_reset(int_vector* v);
bool int_vector_remove(int_vector* v, int value);
void int_vector_remove_index(int_vector* v, unsigned index);
bool int_vector_is_strictly_sorted(int_vector* v);
void int_vector_sort(int_vector* v, int (*compar)(const void *, const void*));
void int_vector_remove_duplicates(int_vector*);
int_vector* int_vector_copy(int_vector*);
bool int_vector_includes_sorted(int_vector*,int_vector*); // compare by subset relation
void int_vector_add_all_sorted(int_vector* add_to, int_vector* to_add); // Adds the elements of the second to the first, sorts in the end
void int_vector_add_all(int_vector* add_to, int_vector* to_add); // Adds the elements of the second to the first
void int_vector_shuffle(int_vector*);
#endif /* int_vector_h */
