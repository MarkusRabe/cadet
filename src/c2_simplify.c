//
//  c2_simplify.c
//  cadet
//
//  Created by Markus Rabe on 02.10.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "cadet_internal.h"
#include "log.h"
#include "mersenne_twister.h"

void c2_delete_learnt_clauses_greater_than(C2* c2, unsigned max_size) {
    unsigned kept = 0;
    unsigned deleted = 0;
    Clause_Iterator ci = qcnf_get_clause_iterator(c2->qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        if (c->original) {
            continue;
        }
        Lit uc = skolem_get_unique_consequence(c2->skolem, c);
        if (c->size > max_size && (uc == 0 || ! skolem_is_deterministic(c2->skolem, lit_to_var(uc))) && c->original == 0) {
            
            if (uc != 0) {
                assert(c2->skolem->stack->push_count == 0); // to make sure the unique consequence reset below does not end up on the stack
                skolem_set_unique_consequence(c2->skolem, c, 0);
            }
            qcnf_unregister_clause(c2->qcnf, c);
            assert(!c->active);
            deleted += 1;
        } else {
            kept += 1;
        }
    }
    V1("  Kept %u; deleted %u clauses\n", kept, deleted);
}

void c2_simplify(C2* c2) {
    assert(c2->restart_base_decision_lvl == c2->skolem->decision_lvl); // because conflicts we may find are treated as UNSAT
    bool simplify_originals = c2->restarts % 15 ? false : true;
    for (unsigned i = 0; i < vector_count(c2->qcnf->active_clauses); i++) {
        if (c2->state != C2_READY) {break;}
        Clause* c = vector_get(c2->qcnf->active_clauses, i);
        if (! c->active || skolem_get_unique_consequence(c2->skolem, c) != 0) {
            continue;
        }
        if (c->original && ! simplify_originals) {
            continue;
        }
        
        Clause* minimized = c2_minimize_clause(c2, c);
        if (minimized) {
            c2_new_clause(c2, minimized);
            if (skolem_is_conflicted(c2->skolem)) {
                c2->state = C2_UNSAT;
                break;
            }
        } else {
            assert(!skolem_is_conflicted(c2->skolem));
        }
        
        // TODO: check if minimized clause subsumes other clauses
        //            if (removed_literals) {
        //                subsumes something else?
        //            }
    }
}
