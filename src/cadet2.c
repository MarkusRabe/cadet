//
//  cadet2.c
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "cadet2.h"
#include "parse.h"
#include "log.h"
#include "util.h"
#include "conflict_analysis.h"
#include "debug.h"
#include "certify.h"
#include "c2_validate.h"
#include "c2_traces.h"
#include "c2_casesplits.h"
#include "skolem_dependencies.h"
#include "c2_cegar.h"
#include "satsolver.h"

#include <math.h>
#include <stdint.h>
#include <sys/time.h>

void c2_init_clauses_and_variables(C2* c2) {
    // initialize the initially deterministic variables; these are usually the universals
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        c2_new_variable(c2, i);
    }
    // search for unit clauses and clauses with unique consequence
    for (unsigned i = 0; i < vector_count(c2->qcnf->clauses); i++) {
        Clause* c = vector_get(c2->qcnf->clauses, i);
        if (c) {c2_new_clause(c2, c);}
    }
}

C2* c2_init_qcnf(QCNF* qcnf, Options* options) {

    C2* c2 = malloc(sizeof(C2));

    c2->qcnf = qcnf;
    c2->options = options;

    c2->decision_vals = val_vector_init();
    c2->state = C2_READY;
    c2->result = CADET_RESULT_UNKNOWN;
    c2->restarts = 0;
    c2->restart_base_decision_lvl = 0;
    c2->activity_factor = (float) 1.0;

    c2->stack = stack_init(c2_undo);
    
    c2->current_conflict = NULL;

    // DOMAINS
    c2->skolem = skolem_init(c2->qcnf, options, vector_count(qcnf->scopes) + 1, 0);
    c2->examples = examples_init(qcnf, options->examples_max_num);

    // Case splits
    c2->case_split_stack = int_vector_init();
    c2->case_split_depth = 0;
    c2->decisions_since_last_conflict = 0;

    // Statistics
    c2->statistics.conflicts = 0;
    c2->statistics.added_clauses = 0;
    c2->statistics.decisions = 0;
    c2->statistics.successful_conflict_clause_minimizations = 0;
    c2->statistics.cases_explored = 0;
    c2->statistics.lvls_backtracked = 0;
    c2->statistics.start_time = get_seconds();

    c2->statistics.failed_literals_stats = statistics_init(10000);
    c2->statistics.failed_literals_conflicts = 0;

    // Magic constants
    c2->magic.initial_restart = options->easy_debugging_mode_c2 ? 6 : 6; // [1..100] // depends also on restart factor
    c2->next_restart = c2->magic.initial_restart;
    c2->magic.restart_factor = (float) 1.2; // [1.01..2]
    c2->magic.conflict_var_weight = 2; // [0..5]
    c2->magic.conflict_clause_weight = 1; // [0..3]
    c2->magic.decision_var_activity_modifier = (float) 0.8; // [-3.0..2.0]
    c2->magic.decay_rate = (float) 0.9;
    c2->magic.implication_graph_variable_activity = (float) 0.5;
    c2->magic.major_restart_frequency = 50;
    c2->next_major_restart = c2->magic.major_restart_frequency;
    c2->magic.num_restarts_before_Jeroslow_Wang = options->easy_debugging_mode_c2 ? 0 : 0;
    c2->magic.num_restarts_before_case_splits = options->easy_debugging_mode_c2 ? 0 : 3;

    // Magic constants for case splits
    c2->magic.skolem_success_horizon = (float) 0.9; // >0.0 && <1.0
    c2->magic.notoriousity_threshold_factor = (float) 5.0; // > 0.0 ??
    c2->magic.skolem_success_recent_average_initialization = (float) 1.0;
    c2->skolem_success_recent_average = c2->magic.skolem_success_recent_average_initialization;
//    c2->case_split_depth_penalty = C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC;
    c2->case_split_depth_penalty = C2_CASE_SPLIT_DEPTH_PENALTY_LINEAR;
    c2->conflicts_between_case_splits_countdown = 1;
    c2->magic.case_split_linear_depth_penalty_factor = options->easy_debugging_mode_c2 ? 1 : 5;

    c2_init_clauses_and_variables(c2);

    return c2;
}

C2* c2_init(Options* options) {
    QCNF* qcnf = qcnf_init();
    C2* c2 = c2_init_qcnf(qcnf,options);
    return c2;
}

void c2_free(C2* c2) {
    statistics_free(c2->statistics.failed_literals_stats);
    skolem_free(c2->skolem);
    val_vector_free(c2->decision_vals);
    stack_free(c2->stack);
    int_vector_free(c2->case_split_stack);
    qcnf_free(c2->qcnf);
    if (c2->current_conflict) {
        int_vector_free(c2->current_conflict);
    }
    free(c2);
}

C2_VAR_DATA c2_initial_var_data() {
    C2_VAR_DATA vd;
    vd.activity = 0.0f;
//    vd.phase = 0;
    return vd;
}

bool c2_is_decision_var(C2* c2, unsigned var_id) {
    return c2_get_decision_val(c2, var_id) != 0;
}

int c2_get_decision_val(C2* c2, unsigned var_id) {
    if (val_vector_count(c2->decision_vals) <= var_id) {
        return 0;
    }
    int val = val_vector_get(c2->decision_vals, var_id);
    assert(val <= 1 && val >= -1);
    return val;
}

void c2_set_decision_val(C2* c2, unsigned var_id, int decision_val) {
    assert(var_id != 0);
    while (var_id >= val_vector_count(c2->decision_vals)) {
        val_vector_add(c2->decision_vals, 0);
    }

    int old_val = val_vector_get(c2->decision_vals, var_id);
    int64_t data = (int64_t) var_id;
    data = data ^ ((int64_t) old_val << 32);
    stack_push_op(c2->stack, C2_OP_ASSIGN_DECISION_VAL, (void*) data);

    val_vector_set(c2->decision_vals, var_id, decision_val);
}

void c2_set_activity(C2* c2, unsigned var_id, float val) {
    assert(val > -0.001);
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    if (v->var_id != 0) {
        assert(v->var_id == var_id);
        v->c2_vd.activity = val * c2->activity_factor;
    }
}

float c2_get_activity(C2* c2, unsigned var_id) {
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    assert(v->var_id == var_id);
    assert(v->c2_vd.activity > -0.001);
    assert(c2->activity_factor >= 1.0);
    return v->c2_vd.activity / c2->activity_factor;
}

void c2_increase_activity(C2* c2, unsigned var_id, float val) {
    assert(val >= 0.0);
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    assert(v->var_id == var_id);
    assert(v->c2_vd.activity > -0.001);
    assert(c2->activity_factor >= 1.0);
    v->c2_vd.activity += val * c2->activity_factor;
}

void c2_scale_activity(C2* c2, unsigned var_id, float factor) {
    assert(factor > 0.0 && factor < 1000.0); // just to be safe
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    assert(v->var_id == var_id);
    assert(v->c2_vd.activity > -0.001);
    assert(c2->activity_factor >= 1.0);
    v->c2_vd.activity *= factor;
}

void c2_rescale_activity_values(C2* c2) {
    float rescale_factor = 1.0f / c2->activity_factor;
    c2->activity_factor = 1.0f;
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (v->var_id != 0) {
            c2_scale_activity(c2, i, rescale_factor);
        }
    }
}

// Returns NULL, if all variables are decided
Var* c2_pick_most_active_notdeterministic_variable(C2* c2) {
    Var* decision_var = NULL;
    float decision_var_activity = -1.0;
    for (unsigned i = 1; i < var_vector_count(c2->qcnf->vars); i++) {
        if (!skolem_is_deterministic(c2->skolem, i)) {
            assert(skolem_get_decision_lvl(c2->skolem, i) == 0);
            Var* v = var_vector_get(c2->qcnf->vars, i);
            assert(!v->is_universal);
            if (v->var_id != 0) {
                assert(v->var_id == i);
                float v_activity = c2_get_activity(c2, v->var_id);
                assert(v_activity > -0.001);
                if (decision_var_activity < v_activity) {
                    decision_var_activity = v_activity;
                    decision_var = v;
                }
            }
        }
    }
    return decision_var;
}


void c2_backtrack_to_decision_lvl(C2 *c2, unsigned backtracking_lvl) {
    V2("Backtrack to level %u\n",backtracking_lvl);
    assert(backtracking_lvl >= 0);
    assert(c2->stack->push_count == c2->skolem->stack->push_count);
    assert(c2->stack->push_count == c2->examples->stack->push_count);
    while (c2->stack->push_count > backtracking_lvl) {
        assert(c2->stack->push_count > 0);
        c2_pop(c2);
    }
}

unsigned c2_are_decisions_involved(C2* c2, int_vector* conflict) {
    unsigned largest_decision_level_involved = c2->restart_base_decision_lvl;
    unsigned max_decision_lvl;
    if (c2->state == C2_SKOLEM_CONFLICT) {
        max_decision_lvl = c2->skolem->decision_lvl;
    } else {
        assert(c2->state == C2_EXAMPLES_CONFLICT);
        PartialAssignment* pa = examples_get_conflicted_assignment(c2->examples);
        max_decision_lvl = pa->decision_lvl;
    }

    for (unsigned i = 0; i < int_vector_count(conflict); i++) {
        Lit lit = int_vector_get(conflict, i);
        unsigned dlvl;
        if (c2->state == C2_SKOLEM_CONFLICT) {
            dlvl = skolem_get_decision_lvl(c2->skolem,lit_to_var(lit));
        } else {
            assert(c2->state == C2_EXAMPLES_CONFLICT);
            PartialAssignment* pa = examples_get_conflicted_assignment(c2->examples);
            dlvl = partial_assignment_get_decision_lvl(pa, lit_to_var(lit));
        }

        if (dlvl > largest_decision_level_involved) {
            largest_decision_level_involved = dlvl;
        }
        assert(largest_decision_level_involved <= max_decision_lvl);
        if (largest_decision_level_involved == max_decision_lvl) {
            break;
        }
    }
    bool res = largest_decision_level_involved > c2->restart_base_decision_lvl;
    assert(! res || c2->skolem->decision_lvl > c2->restart_base_decision_lvl); // Decision involved, but no decision taken
    
    return res;
}

// Returns the second largest decision level that occurs in the conflict. If no second largest decision level exists, returns 0.
unsigned c2_determine_backtracking_lvl(C2* c2, int_vector* conflict) {
    int_vector* dlvls = int_vector_init();
    V2("Decision lvls in conflicted domain:");
    for (unsigned i = 0; i < int_vector_count(conflict); i++) {
        Lit lit = int_vector_get(conflict, i);
        unsigned var_id = lit_to_var(lit);
        unsigned dlvl;
        if (c2->state == C2_SKOLEM_CONFLICT) {
            dlvl = skolem_get_decision_lvl_for_conflict_analysis(c2->skolem, var_id);
        } else {
            assert(c2->state == C2_EXAMPLES_CONFLICT);
            PartialAssignment* pa = examples_get_conflicted_assignment(c2->examples);
            dlvl = partial_assignment_get_decision_lvl(pa, var_id);
        }
        V2(" %u", dlvl);
        int_vector_add(dlvls, (int) dlvl);
    }
    V2("\n");

    int_vector_sort(dlvls, compare_integers_natural_order);

    while (int_vector_count(dlvls) >= 2 &&
           int_vector_get(dlvls, int_vector_count(dlvls) - 1) == int_vector_get(dlvls, int_vector_count(dlvls) - 2)) {
        int_vector_remove_index(dlvls, int_vector_count(dlvls) - 1);
    }
    assert(int_vector_count(dlvls) > 0);
    unsigned second_largest = 0;
    if (int_vector_count(dlvls) == 1) {
        second_largest = 0;
    } else {
        second_largest = (unsigned) int_vector_get(dlvls, int_vector_count(dlvls) - 2);
    }
    second_largest = second_largest < c2->restart_base_decision_lvl ? c2->restart_base_decision_lvl : second_largest;
    return second_largest;
}

void c2_decay_activity(C2* c2) {
    assert(c2->activity_factor > 0);
    assert(isfinite(c2->activity_factor));
    float new_activity_factor = c2->activity_factor / c2->magic.decay_rate;
    if (isfinite(new_activity_factor) && isfinite(1.0 / c2->activity_factor) && new_activity_factor < 1000.0) {
        c2->activity_factor = new_activity_factor;
    } else {
        c2_rescale_activity_values(c2);
        c2->activity_factor *= 1 / c2->magic.decay_rate;
    }
}

void c2_conflict_heuristics(C2* c2, Clause* conflict, unsigned conflicted_var_id) {
    c2_decay_activity(c2);
    for (int i = 0; i < conflict->size; i++) {
        unsigned var_id = lit_to_var(conflict->occs[i]);
        c2_increase_activity(c2, var_id, c2->magic.conflict_clause_weight);
    }
    if (conflicted_var_id != 0) {
        c2_increase_activity(c2, conflicted_var_id, c2->magic.conflict_var_weight);
    }
}

float c2_Jeroslow_Wang_log_weight(vector* clauses) {
    float weight = 0;
    for (unsigned i = 1; i < vector_count(clauses); i++) {
        Clause* c = vector_get(clauses, i);
        if (c->size <= 10) {
            float power = (float) pow(2,(double) c->size);
            weight += 1.0f / power;
        }
    }
    assert(weight >= 0);
    weight += ((float)vector_count(clauses)) * 0.05f;
    return weight;
}

bool c2_is_in_conflcit(C2* c2) {
    bool res =    c2->state == C2_CEGAR_CONFLICT
               || c2->state == C2_EXAMPLES_CONFLICT
               || c2->state == C2_EMPTY_CLAUSE_CONFLICT
               || c2->state == C2_SKOLEM_CONFLICT;
    assert(! res ||   c2->current_conflict);
    assert(  res || ! c2->current_conflict);
    return res;
}

void c2_propagate(C2* c2) {
    assert(c2->current_conflict == NULL);
    
    examples_propagate(c2->examples);
    if (examples_is_conflicted(c2->examples)) {
        assert(c2->state == C2_READY);
        c2->state = C2_EXAMPLES_CONFLICT;
        PartialAssignment* pa = examples_get_conflicted_assignment(c2->examples);
        c2->current_conflict = analyze_assignment_conflict(c2,
                                               pa->conflicted_var,
                                               pa->conflicted_clause,
                                               pa,
                                               partial_assignment_get_value_for_conflict_analysis,
                                               partial_assignment_is_relevant_clause,
                                               partial_assignment_is_legal_dependence,
                                               partial_assignment_get_decision_lvl);
        assert(c2_is_in_conflcit(c2));
        return;
    }
    
    skolem_propagate(c2->skolem);
    if (skolem_is_conflicted(c2->skolem)) {
        assert(c2->state == C2_READY);
        c2->state = C2_SKOLEM_CONFLICT;
        c2->current_conflict = analyze_assignment_conflict(c2,
                                           c2->skolem->conflict_var_id,
                                           c2->skolem->conflicted_clause,
                                           c2->skolem,
                                           skolem_get_value_for_conflict_analysis,
                                           skolem_is_relevant_clause,
                                           skolem_is_legal_dependence_for_conflict_analysis,
                                           skolem_get_decision_lvl_for_conflict_analysis);
        assert(c2_is_in_conflcit(c2));
        return;
    }
}

void c2_initial_propagation(C2* c2) {
    c2_propagate(c2);
    if (! c2_is_in_conflcit(c2)) {
        // Restrict the universals to always satisfy the constraints (derived from AIGER circuits)
        for (unsigned i = 0; i < int_vector_count(c2->qcnf->universals_constraints); i++) {
            unsigned var_id = (unsigned) int_vector_get(c2->qcnf->universals_constraints, i);
            abortif( ! skolem_is_deterministic(c2->skolem, var_id), "Constraint variable is not determinsitic. This should be a constraint purely over the universals.");
            satsolver_add(c2->skolem->skolem, skolem_get_satsolver_lit(c2->skolem, (Lit) var_id));
            satsolver_clause_finished(c2->skolem->skolem);
            skolem_assume_constant_value(c2->skolem, (Lit) var_id);
        }
        c2_propagate(c2); // initial propagation may be extended after assuming constants for constraints
    }
}

// MAIN LOOPS
cadet_res c2_run(C2* c2, unsigned remaining_conflicts) {

    while (remaining_conflicts > 0) {
        V4("\nEntering main loop at dlvl %u.\n", c2->skolem->decision_lvl);

        assert(c2->state == C2_READY);
        assert(c2->skolem->decision_lvl >= c2->restart_base_decision_lvl);
        assert(c2->skolem->decision_lvl <= c2->stack->push_count);
        assert(c2->qcnf->stack->push_count >= c2->skolem->stack->push_count);
        assert(c2->skolem->stack->push_count >= c2->skolem->decision_lvl - c2->restart_base_decision_lvl);

        c2_propagate(c2);
        
        if (c2_is_in_conflcit(c2)) {
            
            unsigned conflicted_var_id = c2->skolem->conflict_var_id; // yep, can be 0; should be cleaned up some time.
            
            c2_print_variable_states(c2);

            remaining_conflicts -= 1;
            c2->statistics.conflicts += 1;
            if (c2->conflicts_between_case_splits_countdown > 0)
                c2->conflicts_between_case_splits_countdown--;
            
            float conflict_success_rating = (float) 1.0 / (((float) int_vector_count(c2->current_conflict)) * ((float) c2->decisions_since_last_conflict) + (float) 1.0);
            c2->skolem_success_recent_average = (float) (c2->skolem_success_recent_average * c2->magic.skolem_success_horizon + conflict_success_rating * (1.0 - c2->magic.skolem_success_horizon));
            c2->decisions_since_last_conflict = 0;

            if (c2_are_decisions_involved(c2, c2->current_conflict)) { // any decisions involved?

                // Update Examples database
                PartialAssignment* new_example = NULL;
                if (c2->skolem->state == SKOLEM_STATE_SKOLEM_CONFLICT) {
                    new_example = examples_add_assignment_from_skolem(c2->examples, c2->skolem);
                    if (new_example && partial_assignment_is_conflicted(new_example)) {
                        assert(c2->result == CADET_RESULT_UNKNOWN);
                        c2->result = CADET_RESULT_UNSAT;
                        c2->state = C2_EXAMPLES_CONFLICT;
                        return c2->result;
                    }
                }

                // Update CEGAR abstraction
                if (c2->options->cegar && c2->skolem->state == SKOLEM_STATE_SKOLEM_CONFLICT) {
                    if (cegar_build_abstraction_for_assignment(c2) != CADET_RESULT_UNKNOWN) {
                        assert(c2->result == CADET_RESULT_UNSAT);
                        return c2->result;
                    }
                }

                unsigned backtracking_lvl = c2_determine_backtracking_lvl(c2, c2->current_conflict);
                unsigned old_dlvl = c2->skolem->decision_lvl;
                c2_backtrack_to_decision_lvl(c2, backtracking_lvl);

                for (unsigned i = 0; i < int_vector_count(c2->current_conflict); i++) {
                    int lit = int_vector_get(c2->current_conflict, i);
                    c2_add_lit(c2, - lit);
                }
                Clause* learnt_clause = qcnf_close_clause(c2->qcnf);

                abortif(learnt_clause == NULL, "Conflict clause could not be created. Conflict counter: %zu", c2->statistics.conflicts);

                learnt_clause->original = false;
                learnt_clause->consistent_with_originals = true;
                assert(skolem_get_unique_consequence(c2->skolem, learnt_clause) == 0);

                if (new_example) {
                    examples_redo(c2->examples, c2->skolem, new_example);
                }
                
                if (skolem_get_unique_consequence(c2->skolem, learnt_clause) != 0) {
                    skolem_bump_conflict_potential(c2->skolem, lit_to_var(skolem_get_unique_consequence(c2->skolem, learnt_clause)));
                }

                c2_log_clause(c2, learnt_clause);
                c2_new_clause(c2, learnt_clause);

                c2_conflict_heuristics(c2, learnt_clause, conflicted_var_id);

                V2("Learnt clause has length %u. Backtracking %u lvls to lvl %u\n", learnt_clause->size, old_dlvl - c2->skolem->decision_lvl, c2->skolem->decision_lvl);
                c2->statistics.lvls_backtracked += old_dlvl - c2->skolem->decision_lvl;
#ifdef DEBUG
                c2_validate_unique_consequences(c2);
#endif
                c2_trace_for_profiling(c2);

                int_vector_free(c2->current_conflict);
                c2->current_conflict = NULL;

                c2->state = C2_READY;

            } else { // Found a refuting assignment
                if (c2->options->functional_synthesis && int_vector_count(c2->current_conflict) > 0) {

                    c2_backtrack_to_decision_lvl(c2, c2->restart_base_decision_lvl);
                    c2->state = C2_READY;

                    V2("Functional synthesis exluded cube.");
                    for (unsigned i = 0; i < int_vector_count(c2->current_conflict); i++) {
                        int lit = int_vector_get(c2->current_conflict, i);
                        int_vector_set(c2->current_conflict, i, - lit);
                    }
                    
                    cegar_new_cube(c2->skolem, c2->current_conflict);
                    
                    V1("Functional synthesis detected a cube of length %u that is over dlvl0 only. We exclude it from future conflict checks.\n", int_vector_count(c2->current_conflict));
                    
                    c2->current_conflict = NULL;
                    
                    continue;
                }

                assert(c2->result == CADET_RESULT_UNKNOWN);
                c2->result = CADET_RESULT_UNSAT;
                return c2->result;
            }

        } else { // No conflict
            // Now case splits and decisions are needed to make further progress.

            if (skolem_can_propagate(c2->skolem)) {
                continue; // can happen when a potentially conflicted variable is not actually conflicted
            }

            // try case splits
            bool progress_through_case_split = c2_case_split(c2);
            if (c2->result != CADET_RESULT_UNKNOWN) { // either the above if statement or c2_case_split may result in SAT/UNSAT
                return c2->result;
            }
            if (progress_through_case_split) {
                assert(c2->conflicts_between_case_splits_countdown > 0);
                continue;
            } // Else continue picking a decision variable. Avoids runnint into a loop where case distinction is tried but nothing happens.

            assert(!skolem_can_propagate(c2->skolem));

            // regular decision
            Var* decision_var = c2_pick_most_active_notdeterministic_variable(c2);

            if (decision_var == NULL) { // no variable could be found
                if (int_vector_count(c2->skolem->potentially_conflicted_variables) == 0) {
                    assert(c2->result == CADET_RESULT_UNKNOWN);
                    c2->result = CADET_RESULT_SAT;
                    return c2->result;
                } else {
                    skolem_global_conflict_check(c2->skolem, false);
                }

            } else { // take a decision
                assert(!skolem_is_conflicted(c2->skolem));

                int phase = 1;
                if (c2->restarts >= c2->magic.num_restarts_before_Jeroslow_Wang) {

                    float pos_JW_weight = c2_Jeroslow_Wang_log_weight(&decision_var->pos_occs);
                    float neg_JW_weight = c2_Jeroslow_Wang_log_weight(&decision_var->neg_occs);

                    phase = pos_JW_weight > neg_JW_weight ? 1 : -1;
                }

                c2_scale_activity(c2, decision_var->var_id, c2->magic.decision_var_activity_modifier);

                // Pushing before the actual decision is important to keep things
                // clean (think of decisions on level 0). This is not a decision yet,
                // so decision_lvl is not yet increased.
                c2_push(c2);

                c2->statistics.decisions += 1;
                c2->decisions_since_last_conflict += 1;

                // examples_decision(c2->examples, value * (Lit) decision_var_id);
                examples_decision_consistent_with_skolem(c2->examples, c2->skolem, phase * (Lit) decision_var->var_id);
                if (examples_is_conflicted(c2->examples)) {
                    V2("Examples domain is conflicted.\n");
                } else {
                    // Regular decision
                    skolem_decision(c2->skolem, phase * (Lit) decision_var->var_id);
                    c2_set_decision_val(c2, decision_var->var_id, phase);
                }
            }

        }
    }

    abortif(c2->result != CADET_RESULT_UNKNOWN, "Expected going into restart but result is not unknown.");
    c2_backtrack_to_decision_lvl(c2, c2->restart_base_decision_lvl);
    return c2->result; // results in a restart
}

cadet_res c2_check_propositional(QCNF* qcnf) {
    V1("Using SAT solver to solve propositional problem.\n");
    SATSolver* checker = satsolver_init();
    satsolver_set_max_var(checker, (int) var_vector_count(qcnf->vars));
    for (unsigned i = 0; i < vector_count(qcnf->clauses); i++) {
        Clause* c = vector_get(qcnf->clauses, i);
        if (c) {
            for (unsigned j = 0; j < c->size; j++) {
                satsolver_add(checker, c->occs[j]);
            }
            satsolver_clause_finished(checker);
        }
    }
    sat_res res = satsolver_sat(checker);
    satsolver_free(checker);
    assert(res == SATSOLVER_RESULT_SAT || res == SATSOLVER_RESULT_UNSAT);
    return res == SATSOLVER_RESULT_SAT ? CADET_RESULT_SAT : CADET_RESULT_UNSAT;
}


void c2_replenish_skolem_satsolver(C2* c2) {
    V1("Replenishing satsolver\n");
    
    // To be sure we did mess up we remember the skolem data structure's decision level and stack height
    assert(c2->skolem->decision_lvl == 0);
    assert(c2->restart_base_decision_lvl == 0);
    assert(c2->skolem->decision_lvl == 0);
    Skolem* old_skolem = c2->skolem;
    
    c2->skolem = skolem_init(c2->qcnf,c2->options,vector_count(c2->qcnf->scopes),0);
    c2_init_clauses_and_variables(c2);
    c2_initial_propagation(c2); // (re-)establishes dlvl 0
    abortif(c2->state != C2_READY, "Conflicted after replenishing.");
    
    cegar_update_interface(c2->skolem);
    
    assert(vector_count(old_skolem->cegar->solved_cubes) == 0 || c2->options->cegar || c2->options->case_splits);
    
    // Copy the cubes that we have solved already.
    for (unsigned i = 0; i < vector_count(old_skolem->cegar->solved_cubes); i++) {
        int_vector* cube = (int_vector*) vector_get(old_skolem->cegar->solved_cubes, i);
        int_vector* cube_copy = int_vector_copy(cube);
        cegar_new_cube(c2->skolem, cube_copy);
    }
    
    c2->skolem->cegar->interface_activities = old_skolem->cegar->interface_activities;
    old_skolem->cegar->interface_activities = NULL;
    
    skolem_free(old_skolem);
    
    abortif(c2_is_in_conflcit(c2) || c2->result != CADET_RESULT_UNKNOWN, "Illegal state afte replenishing");
}


void c2_restart_heuristics(C2* c2) {
    c2->next_restart = (unsigned) (c2->next_restart * c2->magic.restart_factor) + 1;
    c2_rescale_activity_values(c2);
    
    if (c2->next_major_restart == 0) {
        V1("Major restart. Resetting all activity values to 0 and some random ones to 1.\n");
        for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
            c2_set_activity(c2, i, 0.0f);
        }
        assert(c2->activity_factor == 1.0f);
        // bump the activities of some random vars
        for (unsigned i = 1; i <= 100 && i < var_vector_count(c2->qcnf->vars); i++) {
            unsigned random_var_id = (unsigned) (1 + (rand() % ((int)var_vector_count(c2->qcnf->vars) - 1)));
            assert(random_var_id > 0 && random_var_id <= var_vector_count(c2->qcnf->vars));
            if (qcnf_var_exists(c2->qcnf, random_var_id)) {
                c2_increase_activity(c2, random_var_id, 1.0f/(float) i);
            }
        }
        
        V1("Stepping out of case split.\n"); // Needed to simplify replenishing
        
        c2_backtrack_case_split(c2);
        
#if (USE_SOLVER == SOLVER_PICOSAT_ASSUMPTIONS)
        c2_replenish_skolem_satsolver(c2);
#endif

        c2->next_major_restart = c2->magic.major_restart_frequency + (c2->restarts / 4);
        
    } else {
        c2->next_major_restart -= 1;
    }
}

cadet_res c2_sat(C2* c2) {

    if (c2->result != CADET_RESULT_UNKNOWN) {
        return c2->result;
    }

    if (c2->qcnf->empty_clause != NULL) {
        V1("CNF contains an empty clause (clause id %u).\n", c2->qcnf->empty_clause->clause_id);
        c2->result = CADET_RESULT_UNSAT;
        c2->state = C2_EMPTY_CLAUSE_CONFLICT;
        return CADET_RESULT_UNSAT;
    }

    if (qcnf_is_propositional(c2->qcnf) && ! c2->options->use_qbf_engine_also_for_propositional_problems) {
        c2->result = c2_check_propositional(c2->qcnf);
        if (c2->result == CADET_RESULT_UNSAT) {
            c2->state = C2_CEGAR_CONFLICT; // ensures the validation of the conflict does the right thing
        }
        return c2->result;
    }

    ////// THIS RESTRICTS US TO 2QBF
    if (! qcnf_is_2QBF(c2->qcnf) && ! qcnf_is_propositional(c2->qcnf)) {
        V0("Is not 2QBF. Currently not supported.\n");
        return CADET_RESULT_UNKNOWN;
    }
    //////

    for (unsigned i = 0; i < c2->options->initial_examples; i ++) {
        PartialAssignment* pa = examples_add_random_assignment(c2->examples);
        if (pa && partial_assignment_is_conflicted(pa)) {
            break;
        }
    }
    
    c2_initial_propagation(c2);

    if (c2_is_in_conflcit(c2)) {
        c2->result = CADET_RESULT_UNSAT;
        return c2->result;
    }
    
    if (c2->options->miniscoping) {
        c2_analysis_determine_number_of_partitions(c2);
    }
    
    cegar_update_interface(c2->skolem);
    if (c2->options->cegar_only) {
        return cegar_solve_2QBF(c2, -1);
    }

    if (debug_verbosity >= VERBOSITY_HIGH) {
        V1("Deterministic vars on dlvl 0 are:");
        for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
            if (qcnf_var_exists(c2->qcnf, i) && qcnf_is_existential(c2->qcnf, i) && skolem_is_deterministic(c2->skolem, i)) {
                V1(" %u", i);
            }
        }
        V1("\n");
    }

    while (c2->result == CADET_RESULT_UNKNOWN) { // This loop controls the restarts
        c2_run(c2, c2->next_restart);

        while (c2->result == CADET_RESULT_SAT && int_vector_count(c2->case_split_stack) != 0) {
            c2_case_splits_successful_case_completion(c2);
        }
        
        if (c2->result == CADET_RESULT_UNKNOWN) {
            V1("Restart %zu\n", c2->restarts);
            assert(c2->skolem->decision_lvl == c2->restart_base_decision_lvl);
            c2->restarts += 1;
            c2_restart_heuristics(c2);
        }
    }

    return c2->result;
}

/**
 * c2_solve_qdimacs is the traditional entry point to C2. It reads the qdimacs, then solves, then prints and checks the result after calling c2_sat.
 */
cadet_res c2_solve_qdimacs(FILE* f, Options* options) {
    QCNF* qcnf = create_qcnf_from_file(f, options);
    fclose(f);
    abortif(!qcnf,"Failed to create QCNF.");

    if (options->print_qdimacs) {
        qcnf_print_qdimacs(qcnf);
        return 1;
    }

    V1("Maximal variable index: %u\n", var_vector_count(qcnf->vars));
    V1("Number of clauses: %u\n", vector_count(qcnf->clauses));
    V1("Number of scopes: %u\n", vector_count(qcnf->scopes));

    C2* c2 = c2_init_qcnf(qcnf, options);

    c2_sat(c2);

    if (debug_verbosity >= VERBOSITY_LOW) {
        c2_print_statistics(c2);
    }

    switch (c2->result) {
        case CADET_RESULT_UNKNOWN:
            V0("UNKNOWN\n");
            break;
        case CADET_RESULT_SAT:
            V0("SAT\n");
            if (log_qdimacs_compliant) {
                printf("s cnf 1\n");
            }
            break;
        case CADET_RESULT_UNSAT:
            V0("UNSAT\n");
            if (log_qdimacs_compliant) {
                printf("s cnf 0\n");
            }
            break;
    }

    if (c2->result == CADET_RESULT_SAT && c2->options->certify_SAT) {
        c2_cert_AIG_certificate(c2);
    }
    if (c2->result == CADET_RESULT_UNSAT && c2->options->certify_internally_UNSAT) {
        switch (c2->state) {
            case C2_SKOLEM_CONFLICT:
                c2_print_qdimacs_certificate(c2, c2->skolem, skolem_get_value_for_conflict_analysis);
                abortif(! c2_cert_check_UNSAT(c2->qcnf, c2->skolem, skolem_get_value_for_conflict_analysis) , "Check failed! UNSAT result could not be certified.");
                abortif(c2->options->functional_synthesis, "Should not reach UNSAT output in functional synthesis mode.");
                break;
            case C2_CEGAR_CONFLICT:
                c2_print_qdimacs_certificate(c2, c2->skolem, cegar_get_val);
                abortif(! c2_cert_check_UNSAT(c2->qcnf, c2->skolem, cegar_get_val), "Check failed! UNSAT result could not be certified.");
//                abortif(c2->options->functional_synthesis, "Should not reach UNSAT output in functional synthesis mode.");

                break;
            case C2_EXAMPLES_CONFLICT:
                c2_print_qdimacs_certificate(c2, c2->examples, examples_get_value_for_conflict_analysis);
                abortif(! c2_cert_check_UNSAT(c2->qcnf, c2->examples, examples_get_value_for_conflict_analysis) , "Check failed! UNSAT result could not be certified.");
                abortif(c2->options->functional_synthesis, "Should not reach UNSAT output in functional synthesis mode.");
                break;
            case C2_EMPTY_CLAUSE_CONFLICT:
                if (log_qdimacs_compliant) {V0("Unable to provide qdimacs certificate. Found an empty clause, but that may have resulted from universal reduction.\n");}
                abortif(!c2->qcnf->empty_clause || (! c2->qcnf->empty_clause->original && !c2->qcnf->empty_clause->consistent_with_originals), "Inconsistency after empty clause conflict.");
                break;
            default:
                LOG_ERROR("Unknown type of conflict. Such confused, very WOW.");
                abort();
                break;
        }
        if (!log_qdimacs_compliant) {
            V1("Result verified.\n");
        }
    }

    return c2->result;
}

void c2_push(C2* c2) {
    stack_push(c2->stack);
    skolem_push(c2->skolem);
    qcnf_push(c2->qcnf);
    examples_push(c2->examples);
}
void c2_pop(C2* c2) {
    stack_pop(c2->stack, c2);
    skolem_pop(c2->skolem);
    qcnf_pop(c2->qcnf);
    examples_pop(c2->examples);
}
void c2_undo(void* parent, char type, void* obj) {
    C2* c2 = (C2*) parent;
    unsigned var_id = (unsigned) (int64_t) obj; // is 0 in case of type == C2_OP_CASE_SPLIT

    switch ((C2_OPERATION) type) {

        case C2_OP_ASSIGN_DECISION_VAL:
            assert(true);
            int old_val = (int) ((size_t) obj >> 32);
            assert(old_val <= 1 && old_val >= -1);
            val_vector_set(c2->decision_vals, var_id, old_val);
            break;

        case C2_OP_UNIVERSAL_ASSUMPTION:
            assert(true);
            c2_case_splits_undo_assumption(c2, obj);
            break;
            
        default:
            V0("Unknown undo operation in cadet2.c.\n");
            NOT_IMPLEMENTED();
    }
}

Clause* c2_add_lit(C2* c2, Lit lit) {
    if (lit != 0) {
        qcnf_add_lit(c2->qcnf, lit);
        return NULL;
    } else {
        Clause* c = qcnf_close_clause(c2->qcnf);
        if (c) {
            c2_new_clause(c2, c);
        }
        return c;
    }
}

void c2_new_variable(C2* c2, unsigned var_id) {
    Var* v = var_vector_get(c2->qcnf->vars, var_id);
    if (v->var_id != 0 && skolem_is_initially_deterministic(c2->skolem, var_id)) {
        assert(var_id == v->var_id);

        skolem_update_deterministic(c2->skolem, var_id, 1);

        int innerlit = satsolver_inc_max_var(c2->skolem->skolem);
        skolem_update_pos_lit(c2->skolem, var_id, innerlit);
        skolem_update_neg_lit(c2->skolem, var_id, - innerlit);

        union Dependencies dep;
        if (!qcnf_is_DQBF(c2->qcnf)) {
            dep.dependence_lvl = v->scope_id;
        } else {
            dep.dependencies = int_vector_init();
            int_vector_add(dep.dependencies, (int) v->var_id);
        }
        skolem_update_dependencies(c2->skolem, var_id, dep);

        if (v->is_universal) {
            skolem_update_universal(c2->skolem, var_id, 1);
        }
    }
}

void c2_new_clause(C2* c2, Clause* c) {
    c2->result = CADET_RESULT_UNKNOWN;
    examples_new_clause(c2->examples, c);
    skolem_new_clause(c2->skolem, c);
}
