//
//  val_vector.h
//  cadet
//
//  Created by Markus Rabe on 17/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef val_vector_h
#define val_vector_h

#include <stdlib.h>
#include <stdbool.h>

typedef struct {
    char*   data;
    unsigned size;
    unsigned count;
} val_vector;

val_vector* val_vector_init();
val_vector* val_vector_init_at_size(unsigned initial_size);
void val_vector_init_struct(val_vector*, unsigned size);
unsigned val_vector_count(val_vector*);
void val_vector_reduce_count(val_vector*, unsigned);
void val_vector_add(val_vector*, int val);
void val_vector_set(val_vector*, unsigned i, int val);
int  val_vector_get(val_vector*, unsigned);
void val_vector_free(val_vector*);
void val_vector_print(val_vector*);
void val_vector_reset(val_vector*);
void val_vector_remove_last_element(val_vector*);
val_vector* val_vector_copy(val_vector*);
void val_vector_add_all(val_vector* add_to, val_vector* to_add); // Adds the elements of the second to the first

#endif /* val_vector_h */
