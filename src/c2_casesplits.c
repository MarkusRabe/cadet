//
//  c2_casesplits.c
//  cadet
//
//  Created by Markus Rabe on 25/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "c2_casesplits.h"
#include "log.h"
#include "c2_traces.h"
#include "c2_cegar.h"

#include <math.h>

void c2_backtrack_case_split(C2* c2) {
    V2("Backtracking from case split.\n");

    V1("Finished case:");
    for (unsigned i = 0; i < int_vector_count(c2->case_split_stack); i++) {
        V1(" %d", int_vector_get(c2->case_split_stack, i));
    }
    V1("\n");

    c2_backtrack_to_decision_lvl(c2, c2->restart_base_decision_lvl);
    V3("Now popping the case split.\n");
    stack_pop(c2->stack, c2);
    c2_pop(c2);

    c2->skolem->decision_lvl -=1;
    c2->restart_base_decision_lvl -= 1;

    assert(c2->skolem->decision_lvl == 0); // TODO: If we do case splits after dlvl 0, we should also add a real clause
    assert(c2->restart_base_decision_lvl == 0);

    int_vector* solved_cube = int_vector_init();
    vector_add(c2->skolem->cegar->solved_cubes, solved_cube);
    for (unsigned i = 0; i < int_vector_count(c2->case_split_stack); i++) {
        Lit l = int_vector_get(c2->case_split_stack, i);
        assert(skolem_is_deterministic(c2->skolem,lit_to_var(l)));
        assert(skolem_get_constant_value(c2->skolem, l) == 0);
        satsolver_add(c2->skolem->skolem, skolem_get_satsolver_lit(c2->skolem, - l));
        int_vector_add(solved_cube, -l);
    }
    satsolver_clause_finished(c2->skolem->skolem);

    // check learnt clauses for unique consequences ... the last backtracking may have removed the unique consequences
    for (unsigned i = vector_count(c2->qcnf->clauses); i > 0; i--) {
        Clause* c = vector_get(c2->qcnf->clauses, i-1);
        if (c) {
            if (c->original == 1) {
                break;
            }
            if (skolem_get_unique_consequence(c2->skolem, c) == 0) {
                skolem_new_clause(c2->skolem, c);
            }
        }
    }

    int_vector_reset(c2->case_split_stack);

    // Test if we exhausted all cases
    assert(int_vector_count(c2->case_split_stack) == 0);
    if (satsolver_sat(c2->skolem->skolem) == SATSOLVER_UNSATISFIABLE) {
        V1("Universal assignments depleted: SAT\n");
        c2->result = CADET_RESULT_SAT;
    }

}

void c2_case_split_backtracking_heuristics(C2* c2) {
    c2->next_restart = c2->magic.initial_restart;
    
}

// Returns the number of propagations for this assumption
unsigned c2_case_split_assume_constant(C2* c2, Lit lit) {
    assert(!skolem_can_propagate(c2->skolem));
    statistics_start_timer(c2->statistics.failed_literals_stats);

    size_t case_split_decision_metric = c2->skolem->statistics.propagations;

    skolem_push(c2->skolem);
    skolem_assume_constant_value(c2->skolem, lit);
    skolem_propagate(c2->skolem);

    if (skolem_is_conflicted(c2->skolem)) {
        V1("Skolem conflict with assumed constant %d: %d\n", lit, c2->skolem->conflict_var_id);
        c2->statistics.failed_literals_conflicts++;
        case_split_decision_metric = UINT_MAX; //ensure the variable is chosen
    } else {
        V2("Number of propagations when assigning %d: %zu\n", lit, c2->skolem->statistics.propagations - case_split_decision_metric);
        case_split_decision_metric = c2->skolem->statistics.propagations - case_split_decision_metric;
    }

    skolem_pop(c2->skolem);
    statistics_stop_and_record_timer(c2->statistics.failed_literals_stats);

    return (unsigned) case_split_decision_metric;
}

Lit c2_case_split_pick_literal(C2* c2) {
    float max_total = 0.0;
    Lit lit = 0;
    for (unsigned i = 0; i < int_vector_count(c2->skolem->cegar->interface_vars); i++) {
//    }
//    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        assert(int_vector_get(c2->skolem->cegar->interface_vars, i) > 0);
        unsigned var_id = (unsigned) int_vector_get(c2->skolem->cegar->interface_vars, i);
        Var* v = var_vector_get(c2->qcnf->vars, var_id);
        assert(v->var_id == var_id);
        if (var_id != 0
            && skolem_is_deterministic(c2->skolem, var_id)
//            && c2_get_activity(c2, v->var_id) > 1.0
            && skolem_get_constant_value(c2->skolem, (Lit) v->var_id) == 0) {
            
            unsigned propagations_pos = c2_case_split_assume_constant(c2,   (Lit) v->var_id);
            unsigned propagations_neg = c2_case_split_assume_constant(c2, - (Lit) v->var_id);
            
            if (propagations_pos == UINT_MAX || propagations_neg == UINT_MAX) {
                // we found a failed literal
                lit = (propagations_pos > propagations_neg ? 1 : - 1) * (Lit) v->var_id;
                break;
            }
            float combined_quality = ((float) 1.0 + c2_get_activity(c2, v->var_id)) * (float) (propagations_pos * propagations_neg + propagations_pos + propagations_neg);
            assert(propagations_pos < 1000000 && propagations_neg < 1000000); // their product is still a uint
            if (combined_quality > max_total) {
                lit = (propagations_pos > propagations_neg ? 1 : - 1) * (Lit) v->var_id;
                max_total = combined_quality;
            }
        }
    }
    if (debug_verbosity >= VERBOSITY_LOW) {
        V1("Case split literal ");
        options_print_literal_name(c2->options, c2_literal_color(c2, NULL, lit), lit);
        V1(" has quality %.2f\n", max_total);
    }
    return lit;
}

bool c2_case_split(C2* c2) {
    if (! c2->options->case_splits
        || c2->restarts < c2->magic.num_restarts_before_case_splits
        || c2->conflicts_between_case_splits_countdown > 0
        || c2->skolem->decision_lvl != c2->restart_base_decision_lvl) {
        //            && c2->restarts >= c2->magic.num_restarts_before_case_splits
        //            && c2->conflicts_between_case_splits_countdown == 0
        //            && c2->cases_explored == 0 // this limits the case splits to 1!!!
        return false;
    }
    
    assert(!skolem_can_propagate(c2->skolem));

    bool progress = false; // indicates whether this function call changed anything.

//    Lit most_notorious_literal = c2_pick_most_notorious_literal(c2);
    Lit most_notorious_literal = c2_case_split_pick_literal(c2);
    if (most_notorious_literal != 0) {
        unsigned penalty_factor = 1;
        if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_LINEAR) {
            penalty_factor = int_vector_count(c2->case_split_stack);
        }
        if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC) {
            penalty_factor = int_vector_count(c2->case_split_stack) * int_vector_count(c2->case_split_stack);
        }
        if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_EXPONENTIAL) {
            abort(); // not yet implemented
        }
        c2->conflicts_between_case_splits_countdown = c2->conflicts_between_case_splits * (penalty_factor + 1);

        satsolver_assume(c2->skolem->skolem, skolem_get_satsolver_lit(c2->skolem, most_notorious_literal));

        sat_res res = satsolver_sat(c2->skolem->skolem);
        if (res != SATSOLVER_SATISFIABLE) {
            V1("This case admits no assignments to the universals that are consistent with dlvl 0, switching polarity and assuming %d instead.\n", - most_notorious_literal);

            most_notorious_literal = - most_notorious_literal;

            satsolver_assume(c2->skolem->skolem, skolem_get_satsolver_lit(c2->skolem, most_notorious_literal));
            sat_res res = satsolver_sat(c2->skolem->skolem);
            assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl);
            if (res == SATSOLVER_UNSATISFIABLE) {
                V1("Also the SAT check of the other polarity failed. Exhausted the search space on the universal side.\n");
                assert(c2->result == CADET_RESULT_UNKNOWN);
                if (int_vector_count(c2->case_split_stack) == 0) {
                    c2->result = CADET_RESULT_SAT;
                } else {
                    abortif(! c2->options->cegar, "This case can only occur when something else fiddles with the assumptions.");
                    V1("Case split successfully completed through CEGAR-Case Split interaction.\n");
                    c2_backtrack_case_split(c2);
                    c2_case_split_backtracking_heuristics(c2);
                }
                progress = true;
                most_notorious_literal = 0; // suppresses that case split happens
            }
        }

        if (most_notorious_literal != 0) {
            progress = true;
            if (int_vector_count(c2->case_split_stack) == 0) {
                c2->statistics.cases_explored += 1;
                stack_push(c2->stack);
                c2_push(c2);
                c2->skolem->decision_lvl +=1;
                c2->restart_base_decision_lvl += 1;
            }

            int_vector_add(c2->case_split_stack, most_notorious_literal);

            assert(skolem_is_deterministic(c2->skolem, lit_to_var(most_notorious_literal)));
            skolem_assume_constant_value(c2->skolem, most_notorious_literal);

            skolem_propagate(c2->skolem);

            if (skolem_is_conflicted(c2->skolem)) { // actual conflict
                assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl); // otherwise we need to go into conflict analysis
                V1("Case split lead to immediate conflict.\n");
                assert(c2->result == CADET_RESULT_UNKNOWN);
                c2->result = CADET_RESULT_UNSAT;
                c2->state = C2_SKOLEM_CONFLICT;
            }
        }
    } else {
        V1("Case split not successful; no failed literals detected.\n");
    }
    return progress;
}


// Used to determine case splits; is defined as   (number of learnt clauses with same polarity) * activity / ((decision level + 1))
float c2_notoriousity(C2* c2, Lit lit) {
    Var* v = var_vector_get(c2->qcnf->vars, lit_to_var(lit));
    float n = 0.0;
    vector* occs = lit>0 ? &v->pos_occs : &v->neg_occs;
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (! c->original && c->consistent_with_originals) { // is a learnt clause
            n += 1.0;
        }
    }
    n = n * (1 + c2_get_activity(c2, v->var_id));
    return n;
}
float c2_notoriousity_threshold(C2* c2) {
    float cost = 0.0;
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_EXPONENTIAL) {
        cost = powf(2, int_vector_count(c2->case_split_stack));
    }
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC) {
        cost = 1 + int_vector_count(c2->case_split_stack) * int_vector_count(c2->case_split_stack);
    }
    assert(cost >= 1.0);
    // Define 'skolem success' as "decisions to get to a conflict" / conflict clause size (average over recent conflicts).
    float notoriousity_threshold = cost * c2->skolem_success_recent_average * c2->magic.notoriousity_threshold_factor;
    V4("Threshold notoriousity: %.3f\n", notoriousity_threshold);
    return notoriousity_threshold;
}

int c2_pick_most_notorious_literal(C2* c2) {
    Lit notorious_lit = 0;
    float notoriousity = 0.0;
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        if (! skolem_is_deterministic(c2->skolem, i)) {
            continue;
        }
        if (skolem_lit_satisfied(c2->skolem, (int) i) || skolem_lit_satisfied(c2->skolem, - (int) i)) {
            continue;
        }
        if (skolem_get_decision_lvl(c2->skolem, i) != 0) {
            continue;
        }
        //        if (skolem_compare_dependencies(c2->skolem, skolem_get_dependencies(c2->skolem, i), c2->skolem->empty_dependencies) != DEPS_EQUAL) {
        //            continue;
        //        }

        float notoriousity_pos = c2_notoriousity(c2,   (int) i);
        if (notoriousity_pos > notoriousity) {
            notoriousity = notoriousity_pos;
            notorious_lit = (Lit) i;
        }

        float notoriousity_neg = c2_notoriousity(c2, - (int) i);
        if (notoriousity_neg > notoriousity) {
            notoriousity = notoriousity_neg;
            notorious_lit = - (Lit) i;
        }
    }
    return notorious_lit;
}

int_vector* c2_determine_notorious_determinsitic_variables(C2* c2) {

    float notoriousity_threshold = c2_notoriousity_threshold(c2);
    int_vector* notorious_lits = int_vector_init();

    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        if (! skolem_is_deterministic(c2->skolem, i) || skolem_lit_satisfied(c2->skolem, (int) i) || skolem_lit_satisfied(c2->skolem, - (int) i)) {
            continue;
        }

        float notoriousity_pos = c2_notoriousity(c2,   (int) i);
        float notoriousity_neg = c2_notoriousity(c2, - (int) i);
        int more_notorious_val = notoriousity_pos > notoriousity_neg ? 1 : -1; // cannot be notorious in both polarities

        if ( (more_notorious_val > 0 && notoriousity_pos > notoriousity_threshold) || (more_notorious_val < 0 && notoriousity_neg > notoriousity_threshold) ) {
            V1("  Identified %d as notorious (%.3f).\n", - more_notorious_val * (int) i, notoriousity_pos > notoriousity_neg ? notoriousity_pos : notoriousity_neg );
            int_vector_add(notorious_lits, - more_notorious_val * (int) i);
        }
    }
    return notorious_lits;
}
