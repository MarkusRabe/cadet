//
//  pqueue.h
//  cadet
//
//  Created by Markus Rabe on 29/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef pqueue_h
#define pqueue_h

#include "set.h"

#include <stdbool.h>
#include <stdio.h>

//typedef struct { void * data; int pri; } q_elem_t;
//typedef struct {
//    q_elem_t* buf;
//    int n;
//    int alloc;
//    bool unique_computation;
//    set* elements;
//} pqueue;

typedef struct {
    int priority;
    void* data;
} node_t;

typedef struct {
    node_t* nodes;
    int len;
    int size;
    bool unique_computation;
    set* elements;
} pqueue;

pqueue* pqueue_init();
pqueue* pqueue_init_unique_computation();
void pqueue_free(pqueue*);
unsigned pqueue_count(pqueue*);
void pqueue_push(pqueue*, int, void*);
void* pqueue_pop(pqueue*);
//void* pqueue_peek(pqueue*);
//void* pqueue_get(pqueue*, unsigned);
//bool pqueue_contains(pqueue*, void*);
void pqueue_reset(pqueue*);

#endif /* pqueue_h */
