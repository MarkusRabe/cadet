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

void c2_case_split_backtracking_heuristics(C2* c2) {
    c2->next_restart = c2->magic.initial_restart;
//    c2->magic.num_restarts_before_case_splits = (unsigned) c2->restarts + c2->magic.initial_restart;
}

void c2_successful_case_split_heuristics(C2* c2, int_vector* solved_cube) {
    if (c2->case_split_depth < 20) { // prevent tinitiny increments, NaN-hell, etc
        float activity_bump = (float) ((double) 1.0 / pow(2.0, (double) c2->case_split_depth));
        //        float activity_bump = (float) ((double) 1.0 / (double) (c2->case_split_depth * c2->case_split_depth + 1.0));
        V1("Activity bump: %f\n", activity_bump);
        for (unsigned i = 0; i < int_vector_count(solved_cube); i++) {
            unsigned var_id = lit_to_var(int_vector_get(solved_cube, i));
            cegar_add_universal_activity(c2->skolem->cegar, var_id, activity_bump);
        }
//        unsigned last_var_id = lit_to_var(int_vector_get(solved_cube, int_vector_count(solved_cube) - 1));
//        cegar_add_universal_activity(c2->skolem->cegar, last_var_id, activity_bump);
    }
}

// Returns if last assumption was vacuous
void c2_backtrack_case_split(C2* c2) {
    V2("Backtracking from case split.\n");
    
    assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl);
    
    c2_backtrack_to_decision_lvl(c2, 0);
    
    assert(c2->skolem->decision_lvl == 0);
    assert(c2->restart_base_decision_lvl == 0);
    assert(int_vector_count(c2->case_split_stack) == 0);
    
    // Check learnt clauses for unique consequences ... the last backtracking may have removed the unique consequences
    // Can probably be removed once we can add items to deeper levels of the undo-list
    for (unsigned i = vector_count(c2->qcnf->clauses); i > 0; i--) {
        Clause* c = vector_get(c2->qcnf->clauses, i-1);
        if (c) {
            if (c->original == 1) {
                break;
            }
            if (skolem_get_unique_consequence(c2->skolem, c) == 0) {
                c2_new_clause(c2, c);
            }
        }
    }

    skolem_propagate(c2->skolem);
    abortif(skolem_is_conflicted(c2->skolem), "Conflicted after backtracking case split.");
    
    c2_case_split_backtracking_heuristics(c2);
}

// Returns the number of propagations for this assumption
unsigned c2_case_split_probe(C2* c2, Lit lit) {
    assert(!skolem_can_propagate(c2->skolem));
    statistics_start_timer(c2->statistics.failed_literals_stats);

    size_t case_split_decision_metric = c2->skolem->statistics.propagations;

    skolem_push(c2->skolem);
    skolem_assume_constant_value(c2->skolem, lit);
    assert(c2->skolem->mode == SKOLEM_MODE_STANDARD);
    c2->skolem->mode = SKOLEM_MODE_CONSTANT_PROPAGATIONS_TO_DETERMINISTICS;
    skolem_propagate(c2->skolem);
    c2->skolem->mode = SKOLEM_MODE_STANDARD;

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
    float cost_factor_of_max = 0.0;
    Lit lit = 0;
    for (unsigned i = 0; i < int_vector_count(c2->skolem->cegar->interface_vars); i++) {
        unsigned var_id = (unsigned) int_vector_get(c2->skolem->cegar->interface_vars, i);
        assert(int_vector_get(c2->skolem->cegar->interface_vars, i) > 0);
//    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
//        unsigned var_id = i;
        Var* v = var_vector_get(c2->qcnf->vars, var_id);
        assert(v->var_id == var_id);
        if (var_id != 0
            && skolem_is_deterministic(c2->skolem, var_id)
            && skolem_get_constant_value(c2->skolem, (Lit) v->var_id) == 0) {
            
            unsigned propagations_pos = c2_case_split_probe(c2,   (Lit) v->var_id);
            unsigned propagations_neg = c2_case_split_probe(c2, - (Lit) v->var_id);
            
            if (propagations_pos == UINT_MAX || propagations_neg == UINT_MAX) {
                // we found a failed literal
                max_total = 0;
                lit = (propagations_pos > propagations_neg ? 1 : - 1) * (Lit) v->var_id;
                break;
            }
            
            assert(propagations_pos < 1000000 && propagations_neg < 1000000); // avoid overflows
            
            float cost_factor = (float) 1 + (float) 20.0 * /*sqrtf*/(cegar_get_universal_activity(c2->skolem->cegar, v->var_id));
            
            float combined_factor =
                ((float) 1.0
                    + (float) c2_get_activity(c2, v->var_id))
                * cost_factor;
            float combined_quality = combined_factor * (float) (propagations_pos * propagations_neg + propagations_pos + propagations_neg);
            if (combined_quality > max_total) {
                lit = (propagations_pos > propagations_neg ? 1 : - 1) * (Lit) v->var_id;
                max_total = combined_quality;
                cost_factor_of_max = cost_factor;
            }
        }
    }
    if (lit != 0 && debug_verbosity >= VERBOSITY_MEDIUM) {
        V1("Case split literal ");
        options_print_literal_name(c2->options, c2_literal_color(c2, NULL, lit), lit);
        V1(" has quality %.2f, cost factor %.3f, and activity factor %.2f\n",
           max_total,
           cost_factor_of_max,
           ((float) 1.0 + (float) c2_get_activity(c2, lit_to_var(lit))));
    }
    return lit;
}

bool c2_case_splits_make_assumption(C2* c2, Lit lit) {
    
    satsolver_assume(c2->skolem->skolem, skolem_get_satsolver_lit(c2->skolem, lit));
    
    cegar_universal_activity_decay(c2->skolem->cegar, lit_to_var(lit));
    
    bool assumption_vacuous = satsolver_sat(c2->skolem->skolem) != SATSOLVER_SATISFIABLE;
    if (assumption_vacuous) {
        V1("   Vacuous assumption: %d\n", - lit);
        V3("This case admits no assignments to the universals that are consistent with dlvl 0, switching polarity and assuming %d instead.\n", - lit);
        
        lit = - lit;
        
        satsolver_assume(c2->skolem->skolem, skolem_get_satsolver_lit(c2->skolem, lit));
        sat_res res = satsolver_sat(c2->skolem->skolem);
        assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl);
        if (res != SATSOLVER_SATISFIABLE) {
            V1("Also the SAT check of the other polarity failed. Exhausted the search space on the universal side.\n");
            assert(c2->result == CADET_RESULT_UNKNOWN);
            if (int_vector_count(c2->case_split_stack) == 0) {
                c2->result = CADET_RESULT_SAT;
            } else {
                abortif(! c2->options->cegar, "This case can only occur when something else added assumptions.");
//                c2_case_splits_successful_case_completion(c2); // watch out: this might be a recursive call
            }
            lit = 0; // suppresses that case split happens
            return true;
        }
    }
    
    if (lit != 0) {
        
        c2_push(c2);
        c2->skolem->decision_lvl +=1;
        c2->restart_base_decision_lvl += 1;
        int_vector_add(c2->case_split_stack, lit);
        if (!assumption_vacuous) {
            c2->case_split_depth += 1;
        }
        stack_push_op(c2->stack, C2_OP_UNIVERSAL_ASSUMPTION, (void*) (long) assumption_vacuous);
        
        V2("New case split depth is %u\n", c2->case_split_depth);
        
        assert(skolem_is_deterministic(c2->skolem, lit_to_var(lit)));
        skolem_assume_constant_value(c2->skolem, lit);
        
        skolem_propagate(c2->skolem);
        
        if (skolem_is_conflicted(c2->skolem)) { // actual conflict
            assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl); // otherwise we need to go into conflict analysis
            V1("Case split lead to immediate conflict.\n");
            assert(c2->result == CADET_RESULT_UNKNOWN);
            c2->result = CADET_RESULT_UNSAT;
            c2->state = C2_SKOLEM_CONFLICT;
        }
    } else {
        V1("No progress after case split.\n");
    }
    
    assert(satsolver_sat(c2->skolem->skolem) != SATSOLVER_RESULT_UNSAT);
    return assumption_vacuous;
}

void c2_case_splits_reset_countdown(C2* c2) {
    unsigned val = 0;
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_LINEAR) {
        val = c2->case_split_depth * c2->magic.case_split_linear_depth_penalty_factor;
    }
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC) {
        val = c2->case_split_depth * c2->case_split_depth;
    }
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_EXPONENTIAL) {
        abort(); // not yet implemented
    }
    c2->conflicts_between_case_splits_countdown = val + 1;
}

bool c2_case_split(C2* c2) {
    if (! c2->options->case_splits
        || c2->restarts < c2->magic.num_restarts_before_case_splits
        || c2->conflicts_between_case_splits_countdown > 0
        || c2->skolem->decision_lvl != c2->restart_base_decision_lvl) {
        return false;
    }
    
    assert(!skolem_can_propagate(c2->skolem));

    //    Lit most_notorious_literal = c2_pick_most_notorious_literal(c2);
    Lit most_notorious_literal = c2_case_split_pick_literal(c2);
    if (most_notorious_literal != 0) {
        c2_case_splits_make_assumption(c2, most_notorious_literal);
        c2_case_splits_reset_countdown(c2);
        return true;
    } else {
        V1("Case split not successful; no literal available for case split.\n");
        return false;
    }
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
        cost = 1 + powf(2, c2->case_split_depth);
    }
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC) {
        cost = 1 + c2->case_split_depth * c2->case_split_depth;
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

void c2_case_splits_successful_case_completion(C2* c2) {
    assert(c2->result == CADET_RESULT_SAT);
    
    V1("Case split of depth %u successfully completed. ", c2->case_split_depth);
    
    c2->statistics.cases_explored += 1;
    
//    c2_case_split_record_certificate(c2);
    
    c2_backtrack_to_decision_lvl(c2, c2->restart_base_decision_lvl);
    assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl);
    
    c2->result = CADET_RESULT_UNKNOWN;
    
    int_vector* solved_cube = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(c2->case_split_stack); i++) {
        Lit l = int_vector_get(c2->case_split_stack, i);
        int_vector_add(solved_cube, -l);
        V1(" %d", l);
    }
    V1("\n");
    
    // Adjust universal activity values
    assert(c2->case_split_depth <= int_vector_count(solved_cube));
    
    c2_successful_case_split_heuristics(c2, solved_cube);
    
    c2_backtrack_case_split(c2);
    
    cegar_new_cube(c2->skolem, solved_cube);
    
    if (c2->result == CADET_RESULT_UNKNOWN && satsolver_sat(c2->skolem->skolem) == SATSOLVER_RESULT_UNSAT) {
        c2->result = CADET_RESULT_SAT;
    }
    // Redo all but last case assumptions; stop when one turns out to be vacuous (can be in combination with earlier cases.
    bool vacuous = false;
    unsigned i = 0;
    while (! vacuous && c2->result == CADET_RESULT_UNKNOWN) {
        
        if (rand() % 10 == 0) {
            break;
        }
        
        Lit l = int_vector_get(solved_cube, i);
        vacuous = c2_case_splits_make_assumption(c2, - l);
        if (i == int_vector_count(solved_cube) - 1) {
            abortif(!vacuous, "Problem with assumptions after reset");
        }
        i++;
    }
}

void c2_case_splits_undo_assumption(C2* c2, void* obj) {
    bool assumption_vacuous = (bool) (long) obj;
    
    c2->skolem->decision_lvl -=1;
    c2->restart_base_decision_lvl -= 1;
    if (! assumption_vacuous) {
        c2->case_split_depth -= 1;
    }
    int_vector_pop(c2->case_split_stack);
}
