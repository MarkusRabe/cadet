//
//  active_clause_iterator.c
//  cadet
//
//  Created by Markus Rabe on 12.03.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "qcnf.h"

#include <assert.h>

Clause_Iterator qcnf_get_clause_iterator(QCNF* q) {
    Clause_Iterator ci;
    ci.qcnf = q;
    q->clause_iterator_token += 1;
    ci.clause_iterator_token = q->clause_iterator_token;
    ci.idx = 0;
    return ci;
}

Clause* qcnf_next_clause(Clause_Iterator* ci) {
    assert(ci->clause_iterator_token == ci->qcnf->clause_iterator_token);
    while(true) {
        if (ci->idx >= vector_count(ci->qcnf->active_clauses)) {
            assert(ci->idx == vector_count(ci->qcnf->active_clauses));
            return NULL;
        }
        Clause* c = vector_get(ci->qcnf->active_clauses, ci->idx);
        if (c->active) {
            ci->idx += 1;
            return c;
        } else {
            assert(c->in_active_clause_vector);
            c->in_active_clause_vector = 0;
            Clause* tail_clause = vector_pop(ci->qcnf->active_clauses);
            if (tail_clause != c) {
                vector_set(ci->qcnf->active_clauses, ci->idx, tail_clause);
            }
        }
    }
}

