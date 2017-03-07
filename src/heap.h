//
//  heap.h
//  caqe
//
//  Created by Markus Rabe on 06/10/15.
//  Copyright © 2015 Saarland University. All rights reserved.
//

#ifndef heap_h
#define heap_h

#include "vector.h"
#include "set.h"

typedef int (*heap_comparator)(const void*, const void*);

typedef struct {
    heap_comparator	compare;
    vector* vector;
} heap;

heap* heap_init(heap_comparator);
void heap_free(heap*);
unsigned heap_count(heap*);
void heap_push(heap*, void*);
void* heap_pop(heap*);
void* heap_peek(heap*);
void* heap_get(heap*, unsigned);
void heap_test();


// a worklist is a heap with the guarantee that elements are contained at most once, and with efficient membership queries

typedef struct {
    heap* h;
    set* s;
    bool unique_computation;
} worklist;

worklist* worklist_init(heap_comparator);
worklist* worklist_init_unique_computation(heap_comparator);
void worklist_free(worklist*);
unsigned worklist_count(worklist*);
void worklist_push(worklist*, void*);
void* worklist_pop(worklist*);
void* worklist_peek(worklist*);
void* worklist_get(worklist*, unsigned);
bool worklist_contains(worklist*, void*);
void worklist_reset(worklist*);

#endif /* heap_h */
