//
//  heap.c
//  caqe
//
//  Created by Markus Rabe on 06/10/15.
//  Copyright © 2015 Saarland University. All rights reserved.
//

#include "heap.h"
#include "assert.h"
#include "log.h"
#include "mersenne_twister.h"

#include <stdbool.h>

heap* heap_init (heap_comparator compare) {
    heap* h = malloc(sizeof(heap));
    h->vector = vector_init();
    h->compare = compare;
    return h;
}

void heap_free (heap* h) {
    vector_free(h->vector);
    free(h);
}

unsigned heap_count(heap* h) {
    return vector_count(h->vector);
}

int sift_down (heap* h, unsigned min_pos, unsigned pos) {
    void* it = vector_get(h->vector, pos);
    while (pos > min_pos) {
        unsigned parent_pos = (pos - 1) >> 1;
        void* parent = vector_get(h->vector, parent_pos);
        if (h->compare(it, parent) >= 0) {
            break;
        }
        vector_set(h->vector, pos, parent);
        pos = parent_pos;
    }
    vector_set(h->vector, pos, it);
    return 0;
}

int sift_up (heap* h, unsigned pos) {
    unsigned min_pos = pos;
    void* it = vector_get(h->vector, pos);
    unsigned max_pos = vector_count(h->vector) - 1;
    unsigned child_pos = 2 * pos + 1;
    while (child_pos <= max_pos) {
        unsigned right_pos = child_pos + 1;
        void* child = vector_get(h->vector, child_pos);
        if (    right_pos <= max_pos
                &&
                h->compare (child, vector_get(h->vector, right_pos)) >= 0 ) {
            child_pos = right_pos;
        }
        vector_set(h->vector, pos, vector_get(h->vector, child_pos));
        pos = child_pos;
        child_pos = 2 * pos + 1;
    }
    vector_set(h->vector, pos, it);
    return sift_down(h, min_pos, pos);
}

void heap_push (heap* h, void* it) {
    vector_add(h->vector, it);
    unsigned pos = vector_count(h->vector);
    sift_down(h, 0, pos - 1);
}

void* heap_pop (heap* h) {
    if (vector_count(h->vector) <= 0) {
        return NULL;
    } else if (vector_count(h->vector) == 1) {
        void* result_elem = vector_get(h->vector, 0);
        vector_remove_last_element(h->vector);
        return result_elem;
    } else {
        void* result_elem = vector_get(h->vector, 0);
        void* last_elem = vector_get(h->vector, vector_count(h->vector) - 1);
        vector_remove_last_element(h->vector);
        vector_set(h->vector, 0, last_elem);
        sift_up(h, 0);
        return result_elem;
    }
}

void* heap_peek (heap* h) {
    if (vector_count(h->vector) < 1) {
        return NULL;
    }
    return vector_get(h->vector, 0);
}

void* heap_get (heap* h, unsigned pos) {
    if (pos > vector_count(h->vector) - 1) {
        return NULL;
    }
    return vector_get(h->vector, pos);
}

int cmp (const void * a, const void * b) {
    return ( abs((int)a) - abs((int)b) );
}

void heap_test() {
    heap* h = heap_init(cmp);
    
    for (unsigned i = 0; i < 10; i++) {
        int elem = genrand_int31() % 42 - 21;
        V2("%d ", elem);
        heap_push(h, (void*) (long) elem);
    }
    V2("\n");
    vector_print(h->vector);
    for (unsigned i = 0; i < 10; i++) {
        int elem = (int) (long) heap_pop(h);
        V2("%d ", elem);
    }
    V2("\n");
    vector_print(h->vector);
}


worklist* worklist_init_unique_computation(heap_comparator c) {
    worklist* w = worklist_init(c);
    w->unique_computation = true;
    return w;
}

worklist* worklist_init(heap_comparator c) {
    worklist* w = malloc(sizeof(worklist));
    w->h = heap_init(c);
    w->s = set_init();
    w->unique_computation = false;
    return w;
}
void worklist_free(worklist* w) {
    heap_free(w->h);
    set_free(w->s);
    free(w);
}
unsigned worklist_count(worklist* w) {
    assert(w->unique_computation || heap_count(w->h) == set_count(w->s));
    return heap_count(w->h);
}
void worklist_push(worklist* w, void* data) {
    if (!set_contains(w->s, data)) {
        heap_push(w->h, data);
        set_add(w->s, data);
    }
}
void* worklist_pop(worklist* w) {
    void* data = heap_pop(w->h);
    if (!w->unique_computation) {set_remove(w->s, data);}
    return data;
}
void* worklist_peek(worklist* w) {
    return heap_peek(w->h);
}
void* worklist_get(worklist* w, unsigned pos) {
    return heap_get(w->h, pos);
}
bool worklist_contains(worklist* w, void* data) {
    return set_contains(w->s, data);
}
void worklist_reset(worklist* w) {
    vector_reset(w->h->vector);
    set_reset(w->s);
}
