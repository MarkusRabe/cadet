//
//  pqueue.c
//  cadet
//
//  Created by Markus Rabe on 29/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "pqueue.h"
#include "log.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>

pqueue* pqueue_init() {
    pqueue* h = calloc(1, sizeof(pqueue));
    h->unique_computation = false;
    h->elements = set_init();
    return h;
}

pqueue* pqueue_init_unique_computation() {
    pqueue* h = pqueue_init();
    h->unique_computation = true;
    return h;
}

void pqueue_free(pqueue* h) {
    free(h->nodes);
    free(h);
}

void pqueue_reset(pqueue* h) {
    h->size = 0;
    h->len = 0;
    free(h->nodes);
    set_reset(h->elements);
    h->nodes = NULL;
}

unsigned pqueue_count(pqueue* h) {
    assert(h->len >= 0);
    return (unsigned) h->len;
}

void pqueue_push(pqueue* h, int priority, void* data) {
    if (set_contains(h->elements, data)) {
        return;
    } else {
        set_add(h->elements, data);
    }
    if (h->len + 1 >= h->size) {
        h->size = h->size ? h->size * 2 : 4;
        h->nodes = (node_t*)realloc(h->nodes, ((unsigned long) h->size) * sizeof (node_t));
    }
    int i = h->len + 1;
    int j = i / 2;
    while (i > 1 && h->nodes[j].priority > priority) {
        h->nodes[i] = h->nodes[j];
        i = j;
        j = j / 2;
    }
    h->nodes[i].priority = priority;
    h->nodes[i].data = data;
    h->len++;
}

void* pqueue_pop(pqueue* h) {
    int i, j, k;
    if (!h->len) {
        V0("pqueue is empty!\n");
        abort();
    }
    void* data = h->nodes[1].data;
    assert(h->len < h->size);
    h->nodes[1] = h->nodes[h->len];
    h->len--;
    i = 1;
    while (1) {
        k = i;
        j = 2 * i;
        if (j <= h->len && h->nodes[j].priority < h->nodes[k].priority) {
            k = j;
        }
        if (j + 1 <= h->len && h->nodes[j + 1].priority < h->nodes[k].priority) {
            k = j + 1;
        }
        if (k == i) {
            break;
        }
        h->nodes[i] = h->nodes[k];
        i = k;
    }
    h->nodes[i] = h->nodes[h->len + 1];
    if (!h->unique_computation) {
        set_remove(h->elements, data);
    }
    return data;
}
