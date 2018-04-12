//
//  casesplits.c
//  cadet
//
//  Created by Markus Rabe on 25/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "casesplits.h"
#include "log.h"
#include "c2_traces.h"
#include "mersenne_twister.h"

#include <math.h>

// Returns if last assumption was vacuous
void c2_backtrack_casesplit(C2* c2) {
    V2("Backtracking from case split.\n");
    
    assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl);
    
    c2_backtrack_to_decision_lvl(c2, 0);
    c2->restart_base_decision_lvl = 0;
    assert(c2->skolem->decision_lvl == 0);
//    assert(int_vector_count(c2->skolem->universals_assumptions) == 0); // not true in case of AIGer style unremovable assumptions.
    
    // Check learnt clauses for unique consequences ... the last backtracking may have removed the unique consequences
    // Can probably be removed once we can add items to deeper levels of the undo-list;
    // TODO: this is terrible code
    Clause_Iterator ci = qcnf_get_clause_iterator(c2->qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        if (skolem_get_unique_consequence(c2->skolem, c) == 0) {
            c2_new_clause(c2, c);
        }
    }

    skolem_propagate(c2->skolem);
    if (skolem_is_conflicted(c2->skolem)) {
        LOG_WARNING("Conflicted after backtracking case split.");
        assert(c2->state == C2_READY || c2->state == C2_UNSAT);
        c2->state = C2_UNSAT;
    }
    
    c2->next_restart = c2->magic.initial_restart;
    c2->next_major_restart = c2->magic.major_restart_frequency;
    c2->restarts_since_last_major = 0;
}

// Returns the number of propagations for this assumption
unsigned c2_case_split_probe(C2* c2, Lit lit) {
    assert(!skolem_can_propagate(c2->skolem));
    statistics_start_timer(c2->statistics.failed_literals_stats);

    debug_verbosity -= 1;
    
//    size_t case_split_decision_metric = c2->skolem->statistics.propagations;
    size_t case_split_decision_metric = int_vector_count(c2->skolem->determinization_order);
    skolem_push(c2->skolem);
    skolem_make_universal_assumption(c2->skolem, lit);
    
//    if (satsolver_sat(c2->skolem->skolem) == SATSOLVER_RESULT_UNSAT) {
//        V1("Skolem conflict with assumed constant %d: %d\n", lit, c2->skolem->conflict_var_id);
//        case_split_decision_metric = UINT_MAX;
//    } else {
        assert(!c2->skolem->ignore_universal_conflicts);
        c2->skolem->ignore_universal_conflicts = true;
        skolem_propagate(c2->skolem);
        c2->skolem->ignore_universal_conflicts = false;
        
        if (skolem_is_conflicted(c2->skolem)) {
            V2("Skolem conflict with assumed constant %d: %d\n", lit, c2->skolem->conflict_var_id);
            c2->statistics.failed_literals_conflicts++;
            case_split_decision_metric = UINT_MAX; //ensure the variable is chosen
        } else {
            V2("Number of propagations when assigning %d: %zu\n", lit, c2->skolem->statistics.propagations - case_split_decision_metric);
            case_split_decision_metric = int_vector_count(c2->skolem->determinization_order) - case_split_decision_metric;
        }
//    }

    skolem_pop(c2->skolem);
    statistics_stop_and_record_timer(c2->statistics.failed_literals_stats);

    debug_verbosity += 1;
    
    return (unsigned) case_split_decision_metric;
}

Lit c2_case_split_pick_literal(C2* c2) {
    float max_total = 0.0;
    float cost_factor_of_max = 0.0;
    Lit lit = 0;
    for (unsigned i = 1; i < int_vector_count(c2->cs->interface_vars); i++) {
        unsigned var_id = (unsigned) int_vector_get(c2->cs->interface_vars, i);
        assert(int_vector_get(c2->cs->interface_vars, i) > 0);
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
            
            float cost_factor = (float) 1 + (float) 2.0 * /*sqrtf*/(casesplits_get_interface_activity(c2->cs, v->var_id));
            
            float combined_factor =
                ((float) 1.0
                    + (float) c2_get_activity(c2, v->var_id))
                * cost_factor;
            float combined_quality = combined_factor * (float) (propagations_pos * propagations_neg + propagations_pos + propagations_neg + 1);
            if (combined_quality > max_total) {
                lit = (propagations_pos > propagations_neg ? 1 : - 1) * (Lit) v->var_id;
                max_total = combined_quality;
                cost_factor_of_max = cost_factor;
            }
        }
    }
    if (lit != 0 && debug_verbosity >= VERBOSITY_MEDIUM) {
        V1("Case split literal ");
        c2_print_colored_literal_name(c2, c2_literal_color(c2, NULL, lit), lit);
        V1(" has quality %.2f, cost factor %.3f, and activity factor %.2f\n",
           max_total,
           cost_factor_of_max,
           ((float) 1.0 + (float) c2_get_activity(c2, lit_to_var(lit))));
    }
    return lit;
}

void c2_casesplits_reset_countdown(C2* c2) {
    unsigned val = 0;
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_LINEAR) {
        val = int_vector_count(c2->skolem->universals_assumptions) * c2->magic.case_split_linear_depth_penalty_factor;
    }
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC) {
        val = int_vector_count(c2->skolem->universals_assumptions) * int_vector_count(c2->skolem->universals_assumptions);
    }
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_EXPONENTIAL) {
        abort(); // not yet implemented
    }
    c2->conflicts_between_case_splits_countdown = val + 1;
}

bool c2_make_universal_assumption_unless_vacuous(C2* c2, Lit lit) {
    assert(! c2_is_in_conflcit(c2));
    assert(lit);
    
    if (skolem_check_if_domain_is_empty(c2->skolem)) {
        c2->state = C2_CLOSE_CASE; // this case is finished
        return true;
    }
    
    bool is_vacuous = false;
    if (skolem_is_universal_assumption_vacuous(c2->skolem, lit)) {
        is_vacuous = true;
        V1("   Vacuous assumption: %d\n", - lit);
        V3("This case admits no assignments to the universals that are consistent with dlvl 0, switching polarity and assuming %d instead.\n", - lit);
        lit = - lit;
        assert(! c2->options->easy_debugging || ! skolem_is_universal_assumption_vacuous(c2->skolem, lit));
    }
    
    skolem_push(c2->skolem);
    examples_push(c2->examples);
    skolem_increase_decision_lvl(c2->skolem);
    c2->restart_base_decision_lvl += 1;
    
    V1("Entering case %d\n", lit);
    skolem_make_universal_assumption(c2->skolem, lit);
    
    skolem_propagate(c2->skolem);
    
    if (skolem_is_conflicted(c2->skolem)) { // actual conflict
        assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl); // otherwise we need to go into conflict analysis
        V1("Case split lead to immediate conflict. Formula UNSAT\n");
        c2->state = C2_SKOLEM_CONFLICT;
    }
//        abortif(satsolver_sat(c2->skolem->skolem) != SATSOLVER_RESULT_SAT, "Did not detect that domain is empty.");
    return is_vacuous;
}

bool c2_casesplits_assume_single_lit(C2* c2) {
    if (! c2->options->casesplits
        || c2->restarts < c2->magic.num_restarts_before_case_splits
        || c2->conflicts_between_case_splits_countdown > 0
        || c2->skolem->decision_lvl != c2->restart_base_decision_lvl) {
        return false;
    }
    
    assert(!skolem_can_propagate(c2->skolem));

    c2_casesplits_reset_countdown(c2);
    
    //    Lit most_notorious_literal = c2_pick_most_notorious_literal(c2);
    Lit most_notorious_literal = c2_case_split_pick_literal(c2);
    if (most_notorious_literal != 0) {
        c2_make_universal_assumption_unless_vacuous(c2, most_notorious_literal);
        casesplits_decay_interface_activity(c2->cs, lit_to_var(most_notorious_literal));
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
        cost = 1 + powf(2, int_vector_count(c2->skolem->universals_assumptions));
    }
    if (c2->case_split_depth_penalty == C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC) {
        cost = 1 + int_vector_count(c2->skolem->universals_assumptions) * int_vector_count(c2->skolem->universals_assumptions);
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

void c2_close_case(C2* c2) {
    assert(c2->state == C2_CLOSE_CASE);
    
    V1("Case split of depth %u successfully completed.\n", int_vector_count(c2->skolem->universals_assumptions));
    for (unsigned i = 0; i < int_vector_count(c2->skolem->universals_assumptions); i++) {
        V1(" %d", int_vector_get(c2->skolem->universals_assumptions, i));
    }
    V1("\n");
    c2->statistics.cases_closed += 1;
    
    bool completed_casesplit = ! skolem_has_empty_domain(c2->skolem);
    int_vector* determinization_order = NULL;
    int_vector* universal_assumptions = NULL;
    if (completed_casesplit) {
        determinization_order = case_splits_determinization_order_with_polarities(c2->skolem);
        universal_assumptions = int_vector_copy(c2->skolem->universals_assumptions);
    }
    c2_backtrack_to_decision_lvl(c2, c2->restart_base_decision_lvl);
    assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl);
    c2_backtrack_casesplit(c2);
    if (c2_is_in_conflcit(c2)) {
        return;
    }
    if (completed_casesplit) {
        casesplits_encode_closed_case(c2->cs, determinization_order, universal_assumptions);
        
//        // now turn last case split into a clause .. DEACTIVATED due to mysterious drop in performance
//        Case* last_case = vector_get(c2->cs->closed_cases, vector_count(c2->cs->closed_cases) - 1);
//        for (unsigned i = 0; i < int_vector_count(last_case->universal_assumptions); i++) {
//            Lit lit = int_vector_get(last_case->universal_assumptions, i);
//            assert(skolem_is_deterministic(c2->skolem, lit_to_var(lit)));
//            qcnf_add_lit(c2->qcnf, - lit);
//        }
//        Clause* c = qcnf_close_clause(c2->qcnf);
//        abortif(!c, "Case split clause could not be created");
//        c->original = 0;
//        c->consistent_with_originals = 0;
//        c->is_cube = 1;
//        c2_new_clause(c2, c);
        assert(!skolem_is_conflicted(c2->skolem));
        assert(!c2_is_in_conflcit(c2));
    }
    
    assert(c2->skolem->stack->push_count == c2->skolem->decision_lvl);
    if (skolem_check_if_domain_is_empty(c2->skolem)) {
        assert(!c2_is_in_conflcit(c2));
        c2->state = C2_SAT;
    }
}
