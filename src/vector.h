
#ifndef VECTOR_H
#define VECTOR_H

#include <stdbool.h>

typedef struct {
    void** data;
    unsigned size;
    unsigned count;
} vector;


vector* vector_init();
void vector_init_struct(vector* v);
unsigned vector_count(vector* v);
void vector_reduce_count(vector* v, unsigned j);
void vector_add(vector* v, void* value);
void vector_add_sorted(vector* v, void* value);
void vector_set(vector* v, unsigned i, void* value);
void vector_insert_at(vector* v, unsigned i, void* value);
void* vector_get(vector* v, unsigned i);
void* vector_pop(vector* v);
unsigned vector_find(vector* v, void* value);
unsigned vector_find_sorted(vector* v, void* value);
bool vector_contains(vector* v, void* value);
bool vector_contains_sorted(vector* v, void* value);
void vector_free(vector* v);
void vector_print(vector* v);
void vector_reset(vector* v);
bool vector_remove_unsorted(vector* v, void* value);
void vector_remove_index(vector* v, unsigned i);
void vector_remove_last_element(vector* v);
void vector_resize(vector* v, unsigned value);
bool vector_is_sorted(vector* v);
void vector_sort(vector* v);
void vector_remove_duplicates(vector* v);

#endif
