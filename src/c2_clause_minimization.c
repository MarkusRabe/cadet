//
//  c2_clause_minimization.c
//  cadet
//
//  Created by Markus Rabe on 19.09.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "cadet_internal.h"
#include "log.h"
#include "statistics.h"
#include "c2_rl.h"

#include <stdio.h>
#include <assert.h>

//void c2_remove_literals_from_clause(QCNF* qcnf, Clause* c, int_vector* literals) {
//    int_vector_sort(literals, compare_integers_natural_order);
//    for (unsigned i = 0; i < c->size; i++) {
//        Lit l = c->occs[i];
//        if (int_vector_contains_sorted(literals, l)) {
//            bool removed = qcnf_remove_literal(qcnf, c, l);
//            i -= 1;
//            assert(removed);
//        }
//    }
//}

/* Implements two ideas: 
 * (1) remove literals whose negation is implied by the negation of the remaining literals
 * (2) find subset of negations of literals that cause a conflict
 *
 * TODO: Can probably rewrite this; remove requirement that clause must be unregistered and reregistered; use SAT solver and extract unsat core.
 */
Clause* c2_minimize_clause(C2* c2, Clause* c) {
    assert(skolem_get_unique_consequence(c2->skolem, c) == 0);
    assert(c2->minimization_pa->stack->push_count == 0);
    assert(c2->minimization_pa->decision_lvl == 0);
    assert(c->active);
    
    if (!c2->options->minimize_learnt_clauses || c->size <= 1 || skolem_clause_satisfied(c2->skolem, c)) {
        return NULL;
    }
    
    statistics_start_timer(c2->statistics.minimization_stats);
    unsigned initial_size = c->size;
    int_vector* to_remove = int_vector_init();
    int_vector* permutation = int_vector_init(); // Create random permutation of indices of the clause
    
    for (unsigned i = 0; i < c->size; i++) {
        int_vector_add(permutation, (int) i);
    }
    int_vector_shuffle(permutation);
    assert(c->size == int_vector_count(permutation));
    
    partial_assignment_push(c2->minimization_pa);
    for (unsigned i = 0; i < c->size - 1; i++) {
        
        Lit l = c->occs[int_vector_get(permutation, i)];
        int val = partial_assignment_get_value_for_conflict_analysis(c2->minimization_pa, - l);
        
        if (val == 0) {
            partial_assignment_assign_value(c2->minimization_pa, - l);
            partial_assignment_propagate(c2->minimization_pa);
        } else if (val == 1) {
            V3("Removing implied literal %d from clause %u.\n", l, c->clause_idx);
            int_vector_add(to_remove, l);
        }
        
        // TODO: this should actually extract the unsat core, but here we only remove the literals we didn't assume and then do this a couple of more times with other random orderings.
        if (val == -1 || partial_assignment_is_conflicted(c2->minimization_pa)) {
            // Should extract unsat core of assumptions made, but this should also work somewhat:
            for (unsigned j = i+1; j < int_vector_count(permutation); j++) {
                Lit other = c->occs[int_vector_get(permutation, j)];
                int_vector_add(to_remove, other);
            }
            break;
        }
    }
    
    partial_assignment_pop(c2->minimization_pa);
    
    unsigned removed = int_vector_count(to_remove);
    Clause* new_clause = NULL;
    if (removed > 0) {
        qcnf_unregister_clause(c2->qcnf, c);
        for (unsigned i = 0; i < c->size; i++) {
            if (!int_vector_contains(to_remove, c->occs[i])) {
                qcnf_add_lit(c2->qcnf, c->occs[i]);
            }
        }
        new_clause = qcnf_close_clause(c2->qcnf);
        if (new_clause) {
            new_clause->original = 0;
            new_clause->minimized = 1;
            c2_rl_new_clause(new_clause);
            assert(c->size - int_vector_count(to_remove) == new_clause->size);
            V2("Conflict clause minimization removed %u of %u literals.\n", int_vector_count(to_remove), initial_size);
            // Schedule removed literals for pure variable checks
            for (unsigned i = 0; i < int_vector_count(to_remove); i++) {
                skolem_new_variable(c2->skolem, lit_to_var(int_vector_get(to_remove, i)));
            }
        } else {
            V1("Clause minimization led to a duplicate.\n");
            // Schedule all variables in the clause for pure variable checks
            for (unsigned i = 0; i < c->size; i++) {
                skolem_new_variable(c2->skolem, lit_to_var(c->occs[i]));
            }
        }
    } else {
        assert(!skolem_has_unique_consequence(c2->skolem, c));
    }
    
    int_vector_free(permutation);
    int_vector_free(to_remove);
    assert(removed <= c->size);
    statistics_stop_and_record_timer(c2->statistics.minimization_stats);
    c2->statistics.successful_conflict_clause_minimizations += removed;
    
    return new_clause;
}
