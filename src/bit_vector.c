//
//  bit_vector.c
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

#include "bit_vector.h"
#include <stdlib.h>
#include <assert.h>

typedef int64_t word;

#define WORD_BITSIZE 64

// Implement clausal abstraction as bit-vector
struct bit_vector {
    int offset;
    int max;
    int num_words;
    int iteration;
    word* data;
};

bit_vector* bit_vector_init(int num_variables, int num_clauses) {
    bit_vector* ca = malloc(sizeof(bit_vector));
    ca->offset = num_variables + 1;
    ca->max = num_clauses;
    ca->num_words = num_clauses / WORD_BITSIZE + 1;
    ca->data = malloc((size_t) (WORD_BITSIZE * ca->num_words));
    bit_vector_reset(ca);
    return ca;
}

void bit_vector_reset(bit_vector* ca) {
    for (int i = 0; i < ca->num_words; i++) {
        ca->data[i] = 0;
    }
}

void bit_vector_add(bit_vector* ca, int t_lit) {
    int clause_id = t_lit - ca->offset;
    int word_num = clause_id / WORD_BITSIZE;
    int position = clause_id % WORD_BITSIZE;
    ca->data[word_num] |= ((word)1 << position);
}

void bit_vector_remove(bit_vector* ca, int t_lit) {
    int clause_id = t_lit - ca->offset;
    int word_num = clause_id / WORD_BITSIZE;
    int position = clause_id % WORD_BITSIZE;
    ca->data[word_num] &= ~((word)1 << position);
}

bool bit_vector_contains(bit_vector* ca, int t_lit) {
    int clause_id = t_lit - ca->offset;
    int word_num = clause_id / WORD_BITSIZE;
    int position = clause_id % WORD_BITSIZE;
    return ca->data[word_num] & ((word)1 << position);
}

int clausal_abtraction_init_iteration(bit_vector* ca) {
    ca->iteration = 0;
    return bit_vector_next(ca);
}

bool bit_vector_iterate(bit_vector* ca) {
    assert(ca->iteration > 0);
    return ca->iteration - 1 < ca->max;
}

int bit_vector_next(bit_vector* ca) {
    for (int i = ca->iteration; i < ca->max; i++) {
        int word_num = i / WORD_BITSIZE;
        int position = i % WORD_BITSIZE;
        if (ca->data[word_num] == 0) {
            i = WORD_BITSIZE * (word_num + 1) - 1;
            continue;
        }
        if (ca->data[word_num] & ((word)1 << position)) {
            ca->iteration = i + 1;
            return i + ca->offset;
        }
    }
    ca->iteration = ca->max + 1;
    return -1;
}
