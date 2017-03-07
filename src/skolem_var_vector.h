//
//  skolem_var_vector.h
//  cadet
//
//  Created by Markus Rabe on 20/11/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef skolem_var_vector_h
#define skolem_var_vector_h

#include <stdlib.h>
#include <stdbool.h>

struct skolem_var;
typedef struct skolem_var skolem_var;

typedef struct {
    skolem_var*   data;
    unsigned size;
    unsigned count;
} skolem_var_vector;

skolem_var_vector* skolem_var_vector_init();
skolem_var_vector* skolem_var_vector_init_with_size(unsigned);
void skolem_var_vector_init_struct(skolem_var_vector* v, unsigned size);
unsigned skolem_var_vector_count(skolem_var_vector* v);
void skolem_var_vector_reduce_count(skolem_var_vector* v, unsigned j);
void skolem_var_vector_add(skolem_var_vector* v, skolem_var value);
void skolem_var_vector_set(skolem_var_vector* v, unsigned i, skolem_var value);
skolem_var* skolem_var_vector_get(skolem_var_vector* v, unsigned i);
void skolem_var_vector_free(skolem_var_vector* v);
void skolem_var_vector_print(skolem_var_vector* v);
void skolem_var_vector_reset(skolem_var_vector* v);
//bool skolem_var_vector_remove(skolem_var_vector* v, skolem_var value);
//void skolem_var_vector_remove_index(skolem_var_vector* v, unsigned index);
//void skolem_var_vector_sort(skolem_var_vector* v, int (*compar)(const void *, const void*));
skolem_var_vector* skolem_var_vector_copy(skolem_var_vector*);
void skolem_var_vector_add_all(skolem_var_vector* add_to, skolem_var_vector* to_add); // Adds the elements of the second to the first

#endif /* skolem_var_vector_h */
