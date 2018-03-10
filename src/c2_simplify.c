//
//  c2_simplify.c
//  cadet
//
//  Created by Markus Rabe on 02.10.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "cadet2.h"
#include "log.h"
#include "mersenne_twister.h"

void c2_delete_learnt_clauses_greater_than(C2* c2, unsigned max_size) {
    unsigned kept = 0;
    unsigned deleted = 0;
    for (int i = (int) vector_count(c2->qcnf->clauses) - 1; i >= 0; i--) {
        Clause* c = vector_get(c2->qcnf->clauses, (unsigned) i);
        if (! c) {
            continue;
        }
        if (c->original) { // assumes original clauses are in the front of the clause vector :/
            break;
        }
        Lit uc = skolem_get_unique_consequence(c2->skolem, c);
        if (c->size > max_size && (uc == 0 || ! skolem_is_deterministic(c2->skolem, lit_to_var(uc))) && c->original == 0) {
            
            if (uc != 0) {
                assert(c2->skolem->stack->push_count == 0); // to make sure the unique consequence reset below does not end up on the stack
                skolem_set_unique_consequence(c2->skolem, c, 0);
            }
            
            qcnf_delete_clause(c2->qcnf, c);
            assert(vector_get(c2->qcnf->clauses, (unsigned) i) == NULL);
            deleted += 1;
        } else {
            kept += 1;
        }
    }
    V1("  Kept %u; deleted %u clauses\n", kept, deleted);
}

void c2_simplify(C2* c2) {
    assert(c2->restart_base_decision_lvl == c2->skolem->decision_lvl); // because conflicts we may find are treated as UNSAT
    for (int i = (int) vector_count(c2->qcnf->clauses) - 1; i >= 0; i--) {
        Clause* c = vector_get(c2->qcnf->clauses, (unsigned) i);
        if (! c || skolem_get_unique_consequence(c2->skolem, c) != 0) {
            continue;
        }
        if (c->original || genrand_int31() % 100 == 0 || c2->state != C2_READY) {
            break;
        }
        
        skolem_forget_clause(c2->skolem, c);
        c2_minimize_clause(c2, c);
        // Clause can be deleted by clause minimization
        c = vector_get(c2->qcnf->clauses, (unsigned) i);
        if (c) {c2_new_clause(c2, c);}
        
        if (skolem_is_conflicted(c2->skolem)) {
            c2->state = C2_UNSAT;
            break;
        }
        // TODO: check if minimized clause subsumes other clauses
        //            if (removed_literals) {
        //                subsumes something else?
        //            }
    }
}
