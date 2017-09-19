//
//  c2_clause_minimization.c
//  cadet
//
//  Created by Markus Rabe on 19.09.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "cadet2.h"
#include "log.h"
#include "statistics.h"

#include <stdio.h>
#include <assert.h>

void c2_remove_literals_from_clause(QCNF* qcnf, Clause* c, int_vector* literals) {
    int_vector_sort(literals, compare_integers_natural_order);
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        if (int_vector_contains_sorted(literals, l)) {
            vector* occs = qcnf_get_occs_of_lit(qcnf, l);
            bool removed = vector_remove_unsorted(occs, c);
            assert(removed);
            
            for (unsigned j = i+1; j < c->size; j++) {
                c->occs[j-1] = c->occs[j];
            }
        }
    }
}

/* Implements two ideas: 
 * (1) remove literals whose negation is implied by the negation of the remaining literals
 * (2) find subset of negations of literals that cause a conflict
 */
void c2_minimize_clause(C2* c2, Clause* c) {
    assert(skolem_get_unique_consequence(c2->skolem, c) == 0);
    assert(c2->minimization_pa->stack->push_count == 0);
    assert(c2->minimization_pa->decision_lvl == 0);
    
    statistics_start_timer(c2->minimization_stats);
    int_vector* to_remove = int_vector_init();
    
    // Create random permutation of indices of the clause
    int_vector* permutation = int_vector_init();
    for (unsigned i = 0; i < c->size; i++) {
        int_vector_add(permutation, (int) i);
    }
    int_vector_shuffle(permutation);
    
    
    partial_assignment_push(c2->minimization_pa);
    for (unsigned i = 0; i < int_vector_count(permutation); i++) {
        
        Lit l = c->occs[int_vector_get(permutation, i)];
        int val = partial_assignment_get_value_for_conflict_analysis(c2->minimization_pa, l);
        assert(val != -1);
        
        if (val == 0) {
            partial_assignment_assign_value(c2->minimization_pa, - l);
            partial_assignment_propagate(c2->minimization_pa);
            
            for (unsigned j = i+1; j < int_vector_count(permutation); j++) {
                Lit other = c->occs[int_vector_get(permutation, j)];
                if (partial_assignment_get_value_for_conflict_analysis(c2->minimization_pa, other) == 1) {
                    // can be removed
                    int_vector_add(to_remove, other);
                }
            }
        }
        
        if (partial_assignment_is_conflicted(c2->minimization_pa)) {
            // Should extract unsat core of assumptions made, but this should also work somewhat:
            for (unsigned j = i+1; j < int_vector_count(permutation); j++) {
                Lit other = c->occs[int_vector_get(permutation, j)];
                int_vector_add(to_remove, other);
            }
            break;
        }
    }
    partial_assignment_pop(c2->minimization_pa);
    
    c2->statistics.successful_conflict_clause_minimizations += int_vector_count(to_remove);
    V2("Conflict clause minimization removed %u literals.\n", int_vector_count(to_remove));
    
    int_vector_free(permutation);
    int_vector_free(to_remove);
    statistics_stop_and_record_timer(c2->minimization_stats);
}
