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
            bool removed = qcnf_remove_literal(qcnf, c, l);
            i -= 1;
            assert(removed);
        }
    }
}

/* Implements two ideas: 
 * (1) remove literals whose negation is implied by the negation of the remaining literals
 * (2) find subset of negations of literals that cause a conflict
 */
unsigned c2_minimize_clause(C2* c2, Clause* c) {
    statistics_start_timer(c2->statistics.minimization_stats);
    
    if (c->size == 0) {
        return false;
    }
    
    unsigned removed_total = 0;
    unsigned initial_size = c->size;
    
    assert(skolem_get_unique_consequence(c2->skolem, c) == 0);
    assert(c2->minimization_pa->stack->push_count == 0);
    assert(c2->minimization_pa->decision_lvl == 0);
    int_vector* to_remove = int_vector_init();
    
    // Create random permutation of indices of the clause
    int_vector* permutation = int_vector_init();
    
    qcnf_unregister_clause(c2->qcnf, c);
    
    // iterate the minimization a couple of times
    unsigned max_iterations = 1;
    for (unsigned k = 0; k < max_iterations; k++) {
        int_vector_reset(to_remove);
        int_vector_reset(permutation);
        for (unsigned i = 0; i < c->size; i++) {
            int_vector_add(permutation, (int) i);
        }
        int_vector_shuffle(permutation);
        assert(c->size == int_vector_count(permutation));
        
        partial_assignment_push(c2->minimization_pa);
        for (unsigned i = 0; i < int_vector_count(permutation); i++) {
            
            Lit l = c->occs[int_vector_get(permutation, i)];
            int val = partial_assignment_get_value_for_conflict_analysis(c2->minimization_pa, - l);
            
            if (val == 0) {
                partial_assignment_assign_value(c2->minimization_pa, - l);
                partial_assignment_propagate(c2->minimization_pa);
            } else if (val == 1) {
                V3("Removing implied literal %d from clause %u.\n", l, c->clause_id);
                int_vector_add(to_remove, l);
            }
            
            // TODO: this should actually extract the unsat core, but here we only remove the literals we didn't assume and then do this a couple of more times with other random orderings.
            if (val == -1 || partial_assignment_is_conflicted(c2->minimization_pa)) {
                // Should extract unsat core of assumptions made, but this should also work somewhat:
                for (unsigned j = i+1; j < int_vector_count(permutation); j++) {
                    Lit other = c->occs[int_vector_get(permutation, j)];
                    int_vector_add(to_remove, other);
                }
                max_iterations = c->size;
                break;
            }
        }
        partial_assignment_pop(c2->minimization_pa);
        
        assert(int_vector_count(to_remove) <= c->size);
        c2_remove_literals_from_clause(c2->qcnf, c, to_remove);
        removed_total += int_vector_count(to_remove);
        assert(int_vector_count(permutation) - int_vector_count(to_remove) == c->size);
        
        if (int_vector_count(to_remove) == 0) {
            break;
        }
    }

    qcnf_register_clause(c2->qcnf, c);
    
    int_vector_free(permutation);
    int_vector_free(to_remove);
    statistics_stop_and_record_timer(c2->statistics.minimization_stats);
    
    V1("Conflict clause minimization removed %u of %u literals.\n", removed_total, initial_size);
    assert(removed_total < initial_size);
    c2->statistics.successful_conflict_clause_minimizations += removed_total;
    
    return removed_total;
}
