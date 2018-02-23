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
    if (c2->options->minimize_conflicts) {
        for (int i = (int) vector_count(c2->qcnf->clauses) - 1; i >= 0; i--) {
            Clause* c = vector_get(c2->qcnf->clauses, (unsigned) i);
            if (! c || skolem_get_unique_consequence(c2->skolem, c) != 0) {
                continue;
            }
            if (c->original || genrand_int31() % 100 == 0) {
                break;
            }
            
            unsigned removed_literals = c2_minimize_clause(c2, c);
            
            if (c->universal_clause) {
                c2->result = CADET_RESULT_UNSAT;
                c2->state = C2_EMPTY_CLAUSE_CONFLICT;
                break;
            }
            
            // Make sure that if the
            if (removed_literals > 0) {
                bool all_deterministic = true;
                for (unsigned i = 0; i < c->size; i++) {
                    all_deterministic = all_deterministic && skolem_is_deterministic(c2->skolem, lit_to_var(c->occs[i]));
                }
                if (all_deterministic) {
                    for (unsigned i = 0; i < c->size; i++) {
                        int satlit = skolem_get_satsolver_lit(c2->skolem, - c->occs[i]);
                        assert(satlit);
                        satsolver_assume(c2->skolem->skolem, satlit);
                    }
                    sat_res res = satsolver_sat(c2->skolem->skolem);
                    if (res == SATSOLVER_SATISFIABLE) {
                        V1("Clause minimization resulted in a clause consisting only of dlvl0 variables. Terminating.");
                        c2->result = CADET_RESULT_UNSAT;
                        c2->state = C2_CEGAR_CONFLICT;
                        break;
                    }
                }
            }
            
            // TODO: check if minimized clause subsumes other clauses
//            if (removed_literals) {
//                subsumes something else?
//            }
            
            skolem_check_for_unique_consequence(c2->skolem, c);
        }
    }
}
