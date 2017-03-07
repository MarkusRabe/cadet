//
//  var_vector.h
//  cadet
//
//  Created by Markus Rabe on 20/11/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef var_vector_h
#define var_vector_h

#include <stdlib.h>
#include <stdbool.h>

struct Var;
typedef struct Var Var;

typedef struct {
    Var*   data;
    unsigned size;
    unsigned count;
} var_vector;

var_vector* var_vector_init();
void var_vector_resize(var_vector* v, unsigned);
void var_vector_init_struct(var_vector* v);
unsigned var_vector_count(var_vector* v);
void var_vector_reduce_count(var_vector* v, unsigned j);
void var_vector_add(var_vector* v, Var value);
void var_vector_set(var_vector* v, unsigned i, Var value);
Var* var_vector_get(var_vector* v, unsigned i);
void var_vector_free(var_vector* v);
void var_vector_print(var_vector* v);
void var_vector_reset(var_vector* v);
void var_vector_remove_last_element(var_vector* v);
//bool var_vector_remove(var_vector* v, Var value);
//void var_vector_remove_index(var_vector* v, unsigned index);
//void var_vector_sort(var_vector* v, int (*compar)(const void *, const void*));
var_vector* var_vector_copy(var_vector*);
void var_vector_add_all(var_vector* add_to, var_vector* to_add); // Adds the elements of the second to the first

#endif /* var_vector_h */
