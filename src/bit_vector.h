//
//  bit_vector.h
//  caqe
//
//  Copyright (c) 2015, Leander Tentrup, Saarland University
//
//  Permission is hereby granted, free of charge, to any person obtaining
//  a copy of this software and associated documentation files (the
//  "Software"), to deal in the Software without restriction, including
//  without limitation the rights to use, copy, modify, merge, publish,
//  distribute, sublicense, and/or sell copies of the Software, and to
//  permit persons to whom the Software is furnished to do so, subject to
//  the following conditions:
//
//  The above copyright notice and this permission notice shall be
//  included in all copies or substantial portions of the Software.
//
//  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
//  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
//  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
//  IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
//  CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
//  TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
//  SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
//

#ifndef __caqe__bit_vector__
#define __caqe__bit_vector__

#include <stdint.h>
#include <stdbool.h>

typedef struct bit_vector bit_vector;

bit_vector* bit_vector_init(int num_variables, int num_clauses);
void bit_vector_reset(bit_vector*);
void bit_vector_add(bit_vector*, int t_lit);
void bit_vector_remove(bit_vector*, int t_lit);
bool bit_vector_contains(bit_vector*, int t_lit);

// Iteration
int bit_vector_init_iteration(bit_vector*);
bool bit_vector_iterate(bit_vector*);
int bit_vector_next(bit_vector*);


#endif /* defined(__caqe__bit_vector__) */
