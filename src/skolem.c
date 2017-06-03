//
//  skolem.c
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "skolem.h"
#include "function_encoding.h"
#include "skolem_var.h"
#include "skolem_dependencies.h"
#include "log.h"
#include "util.h"
#include "c2_traces.h"
#include "c2_cegar.h"

#include <math.h>
#include <assert.h>
#include <stdint.h>
#include <sys/time.h>

Skolem* skolem_init(QCNF* qcnf, Options* o,
                    unsigned u_initially_deterministic,
                    unsigned e_initially_deterministic) {
    assert(u_initially_deterministic != 0); // indicates wrong usage
    
    Skolem* s = malloc(sizeof(Skolem));
    s->options = o;
    s->qcnf = qcnf;
    s->u_initially_deterministic = u_initially_deterministic;
    s->e_initially_deterministic = e_initially_deterministic;
    
    s->mode = SKOLEM_MODE_STANDARD;
    s->state = SKOLEM_STATE_READY;
    s->decision_lvl = 0;
    
    s->f = f_init(qcnf);
    f_trace_for_profiling_initialize(s->f);
#ifdef SATSOLVER_TRACE
    f_trace_commands(s->f);
#endif
    
    // Define "true"
    s->satlit_true = f_fresh_var(s->f);
    assert(s->satlit_true == 1);
    f_add(s->f, s->satlit_true);
    f_clause_finished(s->f);
    
    s->infos = skolem_var_vector_init_with_size(var_vector_count(qcnf->vars) + var_vector_count(qcnf->vars) / 2); // should usually prevent any resizing of the skolem_var_vector
    s->conflict_var_id = 0;
    s->conflicted_clause = NULL;
    
    if (s->qcnf->problem_type == QCNF_DQBF) {
        s->empty_dependencies.dependencies = int_vector_init();
    } else {
        s->empty_dependencies.dependence_lvl = 0;
    }
    
    s->determinicity_queue = pqueue_init(); // worklist_init(qcnf_compare_variables_by_occ_num);
    s->pure_var_queue = pqueue_init();
    s->unique_consequence = int_vector_init();
    s->deterministic_variables = 0;
    s->stack = stack_init(skolem_undo);
    
    s->clauses_to_check = worklist_init(qcnf_compare_clauses_by_size);
    
    if (s->options->functional_synthesis) {
        s->decision_indicator_sat_lits = int_vector_init();
    }
    
    // Statistics
    s->statistics.propagations = 0;
    s->statistics.explicit_propagations = 0;
    s->statistics.explicit_propagation_conflicts = 0;
    s->statistics.local_determinicity_checks = 0;
    s->statistics.local_conflict_checks = 0;
    s->statistics.global_conflict_checks = 0;
    s->statistics.pure_vars = 0;
    s->statistics.pure_constants = 0;
    
    s->statistics.global_conflict_checks_sat = statistics_init(10000);
    s->statistics.global_conflict_checks_unsat = statistics_init(10000);
    
    // Magic constants
    s->magic.initial_conflict_potential = 0.3f; // [0..1]
    s->magic.conflict_potential_change_factor = 0.81f; // (0..1]
    s->magic.conflict_potential_threshold = 0.8f; // (0..1)
    s->magic.conflict_potential_offset = 0.00f;
    s->magic.blocked_clause_occurrence_cutoff = 20;
    
    return s;
}

void skolem_free(Skolem* s) {
    f_free(s->f);
    skolem_var_vector_free(s->infos);
    pqueue_free(s->determinicity_queue);
    pqueue_free(s->pure_var_queue);
    worklist_free(s->clauses_to_check);
    int_vector_free(s->unique_consequence);
    if (s->options->functional_synthesis) {
        int_vector_free(s->decision_indicator_sat_lits);
    }
    stack_free(s->stack);
    free(s);
}

void skolem_push(Skolem* s) {
    
    stack_push(s->stack);
    f_push(s->f);
    abortif(pqueue_count(s->determinicity_queue) != 0, "s->determinicity_queue nonempty upon push. Serious because the remaining elements might be forgotten to be tracked upon a pop.");
    abortif(pqueue_count(s->pure_var_queue), "s->pure_var_queue nonempty on push. Serious because the remaining elements might be forgotten to be tracked upon a pop.");
    abortif(worklist_count(s->clauses_to_check) != 0, "s->clauses_to_check nonempty upon push. Serious because the remaining elements might be forgotten to be tracked upon a pop.");
}
void skolem_pop(Skolem* s) {
    assert(!skolem_is_conflicted(s));
    if (worklist_count(s->clauses_to_check) > 0) {
        worklist_reset(s->clauses_to_check);
    }
    if (pqueue_count(s->determinicity_queue) > 0) {
        pqueue_reset(s->determinicity_queue);
    }
    if (pqueue_count(s->pure_var_queue) > 0) {
        pqueue_reset(s->pure_var_queue);
    }
    
    stack_pop(s->stack, s);
    f_pop(s->f);
}
void skolem_recover_from_conflict(Skolem* s) {
    abortif(!skolem_is_conflicted(s), "Skolem domain expected to be in conflicted state.");
    switch (s->state) {
        case SKOLEM_STATE_SKOLEM_CONFLICT:
            assert(s->conflict_var_id != 0);
            assert(s->conflicted_clause == NULL);
            f_pop(s->f); // to compensate the push before the SAT call
            s->state = SKOLEM_STATE_READY;
            s->conflict_var_id = 0;
            break;
        case SKOLEM_STATE_CONSTANTS_CONLICT:
            assert(s->conflict_var_id != 0);
            assert(s->conflicted_clause != NULL);
            s->state = SKOLEM_STATE_READY;
            s->conflict_var_id = 0;
            s->conflicted_clause = NULL;
            break;
        default:
            break;
    }
}

void skolem_new_clause(Skolem* s, Clause* c) {
    abortif(c == NULL, "Clause pointer is NULL in skolem_new_clause.\n");
    skolem_check_for_unique_consequence(s, c);
    if (c->size == 1) {
        worklist_push(s->clauses_to_check, c);
    }
}

bool skolem_is_initially_deterministic(Skolem* s, unsigned var_id) {
    Var* v = var_vector_get(s->qcnf->vars, var_id);
    return v->scope_id < (v->is_universal ? s->u_initially_deterministic : s->e_initially_deterministic);
}

// Approximation, not accurate. Functions may be constant true but we don't necessarily detect that.
bool skolem_lit_satisfied(Skolem* s, Lit lit) {
    skolem_var si = skolem_get_info(s, lit_to_var(lit));
    if (lit > 0) {
        return si.pos_lit == s->satlit_true;
    } else {
        return si.neg_lit == s->satlit_true;
    }
}

bool skolem_clause_satisfied(Skolem* s, Clause* c) {
    for (int i = c->size - 1; i >= 0; i--) {
        if (skolem_lit_satisfied(s, c->occs[i])) {
            return true;
        }
    }
    return false;
}
bool skolem_is_conflicted(Skolem* s) {
    assert(s->state != SKOLEM_STATE_CONSTANTS_CONLICT || (s->conflict_var_id == 0) == (s->conflicted_clause == NULL));
    assert(s->conflict_var_id != 0 || s->state == SKOLEM_STATE_READY);
    assert(s->conflict_var_id == 0 || s->state != SKOLEM_STATE_READY);
    return s->conflict_var_id != 0;
}
bool skolem_can_propagate(Skolem* s) {
    return (worklist_count(s->clauses_to_check) || pqueue_count(s->determinicity_queue) || pqueue_count(s->pure_var_queue))
           && ! skolem_is_conflicted(s);
}

// Returns false, if the lit is undefined. Otherwise returns satsolver lit corresponding to the lit-definition.
int skolem_get_satlit(Skolem* s, Lit lit) {
    assert(lit != 0);
    skolem_var si = skolem_get_info(s, lit_to_var(lit));
    if (lit > 0) {
        return si.pos_lit;
    } else {
        return si.neg_lit;
    }
}

struct UNIQUE_CONSEQUENCE_UNDO_INFO;
typedef struct UNIQUE_CONSEQUENCE_UNDO_INFO UNIQUE_CONSEQUENCE_UNDO_INFO;

// The union is needed for casting between int64 and the decision_struct
typedef union {
    struct {
        unsigned clause_id;
        Lit lit;
    } components;
    int64_t data;
} UNIQUE_CONSEQUENCE_UNDO_INFO_UNION;

void skolem_set_unique_consequence(Skolem* s, Clause* c, Lit l) {
    V3("  Assigning clause %d unique consequence %d\n", c->clause_id, l);
    while (int_vector_count(s->unique_consequence) <= c->clause_id) {
        int_vector_add(s->unique_consequence, 0);
    }
    UNIQUE_CONSEQUENCE_UNDO_INFO_UNION ucui;
    ucui.components.clause_id = c->clause_id;
    ucui.components.lit = int_vector_get(s->unique_consequence, c->clause_id);
    
    assert(ucui.components.lit != l);
    
    stack_push_op(s->stack, SKOLEM_OP_UNIQUE_CONSEQUENCE, (void*) (uint64_t) ucui.data); // (uint64_t) c->clause_id
    int_vector_set(s->unique_consequence, c->clause_id, l);
}

Lit skolem_get_unique_consequence(Skolem* s, Clause* c) {
    if (int_vector_count(s->unique_consequence) > c->clause_id) {
        return int_vector_get(s->unique_consequence, c->clause_id);
    } else {
        return 0;
    }
}

bool skolem_has_unique_consequence(Skolem* s, Clause* c) {
    return skolem_get_unique_consequence(s, c) != 0;
}

void skolem_check_occs_for_unique_consequences(Skolem* s, Lit lit) {
    assert(lit != 0);
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        
        if (skolem_has_unique_consequence(s,c)) {  // || partial_assignment_is_clause_satisfied(pa, c) // we are ignoring the possibility that the clause might be satisfied ..
            continue;
        }
        skolem_check_for_unique_consequence(s, c);
    }
}

void skolem_check_for_unique_consequence(Skolem* s, Clause* c) {
    assert(!skolem_has_unique_consequence(s,c));
    Lit undecided_lit = 0;
    for (int i = c->size - 1; i >= 0; i--) {
        int lit = c->occs[i];
        if (! skolem_is_deterministic(s, lit_to_var(lit))) {
            if (undecided_lit == 0) {
                undecided_lit = c->occs[i];
            } else {
                return;
            }
        }
    }
    
    if (undecided_lit != 0) {
        skolem_set_unique_consequence(s, c, undecided_lit);
        Var* unique = var_vector_get(s->qcnf->vars, lit_to_var(undecided_lit));
        pqueue_push(s->determinicity_queue,
                    (int) (vector_count(&unique->pos_occs) + vector_count(&unique->neg_occs)),
                    (void*) (size_t) unique->var_id);
    }
}

/*
 * This function extends the definition of variable v by a configurable selection of clauses.
 * Only clauses with unique consequence var_id or -var_id are admitted.
 *
 * The flag skip_v_occurrences allows to suppress adding the occurrences of var_id and -var_id,
 * which is used for determinicity checks.
 */
bool skolem_add_occurrences_for_determinicity_check(Skolem* s, SATSolver* sat,
                                           unsigned var_id, vector* occs) {
    bool case_exists = false;
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        Lit unique_consequence = skolem_get_unique_consequence(s, c);
        
        if (lit_to_var(unique_consequence) == var_id
                && ! skolem_has_illegal_dependence(s,c)) {
            for (unsigned i = 0; i < c->size; i++) {
                if (lit_to_var(c->occs[i]) != var_id && ! skolem_lit_satisfied(s, - c->occs[i])) {
                    satsolver_add(sat, c->occs[i]);
                }
            }
            satsolver_clause_finished(sat);
            case_exists = true;
        }
    }
    return case_exists;
}

bool skolem_check_for_local_determinicity(Skolem* s, Var* v) {
    assert(!skolem_is_deterministic(s, v->var_id));
    assert(qcnf_is_existential(s->qcnf,v->var_id));
    
    V3("Checking local determinicity of var %d: ", v->var_id);
    s->statistics.local_determinicity_checks++;
    
    SATSolver* sat = satsolver_init();
    satsolver_set_max_var(sat, (int) var_vector_count(s->qcnf->vars));
    skolem_add_occurrences_for_determinicity_check(s, sat, v->var_id, &v->pos_occs);
    skolem_add_occurrences_for_determinicity_check(s, sat, v->var_id, &v->neg_occs);
    int result = satsolver_sat(sat);
    satsolver_free(sat);
    
    if (result == SATSOLVER_SATISFIABLE) {
        V3("not deterministic\n");
    } else {
        V3("deterministic\n");
    }
    return result != SATSOLVER_SATISFIABLE;
}

// Check if literal is blocking for all clauses where it is a unique consequence. See blocked clause elimination.
bool skolem_clause_satisfied_when_in_doubt(Skolem* s, Clause* c, Lit lit) {
    assert(qcnf_is_existential(s->qcnf, lit_to_var(lit)));
    assert(qcnf_contains_literal(c, lit));
    assert(! skolem_clause_satisfied(s, c)); // No problem, but it does not make sense to call this function
    vector* opp_occs = qcnf_get_occs_of_lit(s->qcnf, - lit);
    if (vector_count(opp_occs) > s->magic.blocked_clause_occurrence_cutoff) {
        return false;
    }
    for (unsigned i = 0; i < vector_count(opp_occs); i++) {
        Clause* other = vector_get(opp_occs, i);
        assert(qcnf_contains_literal(other, - lit));
        if (skolem_get_unique_consequence(s, other) == - lit && ! skolem_clause_satisfied(s, other) && qcnf_antecedent_subsubsumed(s->qcnf, other, c, lit_to_var(lit))) {
            return true;
        }
    }
    return false;
}

/* Is there a clause containing this lit, but this lit is not a UC?
 * 
 * options->enhanced_pure_literals :
 * Disregarding clauses that are satisfied whenever a UC of -lit fires.
 */
bool skolem_is_lit_pure(Skolem* s, Lit lit) {
    if (! s->options->propagate_pure_literals) {return false;}
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if ((skolem_get_unique_consequence(s, c) != lit || skolem_has_illegal_dependence(s, c) ) && ! skolem_clause_satisfied(s, c) // std condition for pure vars
            && (! s->options->enhanced_pure_literals || ! skolem_clause_satisfied_when_in_doubt(s, c, lit)))         // can consider variable as pure, when the UCs are blocked by this literal
        {
            return false;
        }
    }
    return true;
}

void skolem_add_unique_antecedents_of_v_local_conflict_check(Skolem* s, SATSolver* sat, Lit lit) {
    
    int_vector* conjunction_vars = int_vector_init();
    
    vector* occs = qcnf_get_occs_of_lit(s->qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (lit_to_var(skolem_get_unique_consequence(s, c)) == lit_to_var(lit)) {
            switch (c->size) {
                case 1:
                    // This is a tricky one: as long as the conjunction vars have not been asserted in
                    // the second for-loop below, this function call (of
                    // skolem_add_unique_antecedents_of_v_local_conflict_check) does not actually restrict
                    // the sat instance at all. Returning thus effectively cancels this call.
                    int_vector_free(conjunction_vars);
                    return;
                    
                    //                case 2:
                    //                    // We don't need a conjunction_var, but screw it.
                    //                    break;
                    
                default:
                    assert(c->size != 0);
                    int conjunction_var = satsolver_inc_max_var(sat);
                    int_vector_add(conjunction_vars, conjunction_var);
                    
                    for (int j = 0; j < c->size; j++) {
                        Lit inner = c->occs[j];
                        if (lit_to_var(inner) != lit_to_var(lit) && skolem_may_depend_on(s, lit_to_var(lit), lit_to_var(inner))) {
                            if (skolem_lit_satisfied(s, inner)) {
                                assert( ! skolem_lit_satisfied(s, - inner));
                                satsolver_add(sat, conjunction_var);
                                satsolver_clause_finished(sat);
                                break; // this antecedent can never be true.
                            } else {
                                assert(skolem_is_deterministic(s, lit_to_var(inner)));
                                satsolver_add(sat, skolem_get_satlit(s, - inner));
                                satsolver_add(sat, conjunction_var);
                                satsolver_clause_finished(sat);
                            }
                        }
                    }
                    break;
            }
        }
    }
    
    for (unsigned i = 0; i < int_vector_count(conjunction_vars); i++) {
        int satlit = int_vector_get(conjunction_vars, i);
        satsolver_add(sat, - satlit);
    }
    satsolver_clause_finished(sat);
    
    int_vector_free(conjunction_vars);
}

bool skolem_is_locally_conflicted(Skolem* s, unsigned var_id) {
    assert(qcnf_is_existential(s->qcnf, var_id));
    
    V3("Checking for conflicts for var %d:", var_id);
    s->statistics.local_conflict_checks++;
    
    SATSolver* sat = satsolver_init();
    satsolver_set_max_var(sat, f_get_max_var(s->f));
    satsolver_add(sat, s->satlit_true);
    satsolver_clause_finished(sat);
    skolem_add_unique_antecedents_of_v_local_conflict_check(s, sat,   (Lit) var_id);
    skolem_add_unique_antecedents_of_v_local_conflict_check(s, sat, - (Lit) var_id);
    //    if (debug_verbosity >= VERBOSITY_ALL) {
    //        satsolver_print(sat);
    //    }
    sat_res result = satsolver_sat(sat);
    satsolver_free(sat);
    if (result == SATSOLVER_SATISFIABLE) {
        V3(" locally conflicted\n");
    } else {
        V3(" not (locally) conflicted\n");
    }
    return result == SATSOLVER_SATISFIABLE;
}

void skolem_propagate_determinicity(Skolem* s, unsigned var_id) {
    assert(!skolem_is_conflicted(s));
    V4("Propagating determinicity for var %u\n", var_id);
    
    if (skolem_is_deterministic(s, var_id)) {
        return;
    }
    if (qcnf_is_universal(s->qcnf, var_id)) {
        abortif(s->mode != SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS,"Universal ended up in determinicity propagation queue. This should not happen in normal mode.");
        return;
    }
    
    Var* v = var_vector_get(s->qcnf->vars, var_id);
    assert(v->var_id == var_id);
    
    if (skolem_check_for_local_determinicity(s, v)) {
        V3("Var %u is deterministic.\n", var_id);
        s->statistics.propagations += 1;
        
        skolem_update_decision_lvl(s, var_id, s->decision_lvl);
        
        bool locally_conflicted = skolem_is_locally_conflicted(s, var_id);
        if ( ! locally_conflicted) {
            int satlit = f_fresh_var(s->f);
            skolem_update_satlit(s, (Lit) var_id,   satlit); // must be done before the two next calls to make 'satlit' available in the skolem_var
            skolem_update_satlit(s, - (Lit) var_id, - satlit);
            skolem_update_deterministic(s, var_id, 1); // should happen before
            
            f_add_clauses(s, var_id, &v->pos_occs);
            f_add_clauses(s, var_id, &v->neg_occs);
            
        } else { // add clauses with unique consequence as partial function
            
            f_encode_unique_antecedents_for_lits(s, (Lit)   (int) var_id, false);
            f_encode_unique_antecedents_for_lits(s, (Lit) - (int) var_id, false);
            
            skolem_update_deterministic(s, var_id, 1);
        }
        
        /* Update depencendies and propagation queues before global conflict check,
         * because even when the conflict check is successful, opportunistic
         * CEGAR might handle the conflict, and we then continue propagating.
         */
        skolem_update_dependencies(s, var_id, skolem_compute_dependencies(s,var_id));
        skolem_check_occs_for_unique_consequences(s,   (Lit) var_id);
        skolem_check_occs_for_unique_consequences(s, - (Lit) var_id);
        
        if (locally_conflicted) {
            skolem_global_conflict_check(s, var_id);
            if (skolem_is_conflicted(s)) {
                return;
            }
        }
        
    } else {
        pqueue_push(s->pure_var_queue,
                    (int)(vector_count(&v->pos_occs) + vector_count(&v->neg_occs)),
                    (void*) (size_t) var_id);
    }
}

void skolem_propagate_pure_variable(Skolem* s, unsigned var_id) {
    if (skolem_is_deterministic(s, var_id)) {
        return;
    }
    if (qcnf_is_universal(s->qcnf, var_id)) {
        abortif(s->mode != SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS,"Universal ended up in determinicity propagation queue. This should not happen in normal mode.");
        return;
    }
    
    Var* v = var_vector_get(s->qcnf->vars, var_id);
    assert(v->var_id == var_id);
    
    // Check for pure literal rule
    int pure_polarity = 0;
    if (skolem_is_lit_pure(s,   (Lit) var_id)) {
        pure_polarity = 1;
    } else if (skolem_is_lit_pure(s, - (Lit) var_id)) {
        pure_polarity = -1;
    }
    if (pure_polarity != 0) {
        V3("Detected var %u as pure: %d\n", var_id, pure_polarity);
        s->statistics.propagations += 1;
        s->statistics.pure_vars += 1;
        skolem_update_decision_lvl(s, var_id, s->decision_lvl);
        bool locally_conflicted = skolem_is_locally_conflicted(s, var_id);
        if ( ! locally_conflicted) {
            f_encode_unique_antecedents_for_lits(s, pure_polarity * (Lit) var_id, true);
            skolem_var si = skolem_get_info(s, var_id);
            
            // also triggers checks for new unique consequences
            if (pure_polarity > 0) {
                assert(vector_count(&v->pos_occs) == 0 || si.pos_lit != 0);
                skolem_update_satlit(s, - (Lit) var_id, - si.pos_lit);
                skolem_update_deterministic(s, var_id, 1);
                skolem_update_pure_pos(s, var_id, 1);
            } else {
                assert(vector_count(&v->neg_occs) == 0 || si.neg_lit != 0);
                skolem_update_satlit(s, (Lit) var_id, - si.neg_lit);
                skolem_update_deterministic(s, var_id, 1);
                skolem_update_pure_neg(s, var_id, 1);
            }
        } else {
            // pure and locally conflicted
            f_encode_unique_antecedents_for_lits(s,   pure_polarity * (Lit) var_id, true);
            f_encode_unique_antecedents_for_lits(s, - pure_polarity * (Lit) var_id, false); // note that the other side is not defined both sided
            
            skolem_var si = skolem_get_info(s, var_id);
            int new_opposite_sat_lit = f_fresh_var(s->f);
            if (pure_polarity > 0) {
                assert(vector_count(&v->pos_occs) == 0 || si.pos_lit != 0);
                
                // define the remaining cases false
                f_add(s->f, - skolem_get_satlit(s,   (Lit) var_id));
                f_add(s->f,   skolem_get_satlit(s, - (Lit) var_id));
                f_add(s->f, - new_opposite_sat_lit);
                f_clause_finished(s->f);
                
                if (s->options->functional_synthesis) {
                    f_add(s->f,   skolem_get_satlit(s,   (Lit) var_id));
                    f_add(s->f,   new_opposite_sat_lit);
                    f_clause_finished(s->f);
                    
                    f_add(s->f, - skolem_get_satlit(s, - (Lit) var_id));
                    f_add(s->f,   new_opposite_sat_lit);
                    f_clause_finished(s->f);
                }
                
                skolem_update_satlit(s, - (Lit) var_id, new_opposite_sat_lit);
                skolem_update_deterministic(s, var_id, 1);
                skolem_update_pure_pos(s, var_id, 1);
            } else {
                assert(vector_count(&v->neg_occs) == 0 || si.neg_lit != 0);
                
                // define the remaining cases false
                f_add(s->f, - skolem_get_satlit(s, - (Lit) var_id));
                f_add(s->f,   skolem_get_satlit(s,   (Lit) var_id));
                f_add(s->f, - new_opposite_sat_lit);
                f_clause_finished(s->f);
                
                if (s->options->functional_synthesis) {
                    f_add(s->f,   skolem_get_satlit(s, - (Lit) var_id));
                    f_add(s->f,   new_opposite_sat_lit);
                    f_clause_finished(s->f);
                    
                    f_add(s->f, - skolem_get_satlit(s,   (Lit) var_id));
                    f_add(s->f,   new_opposite_sat_lit);
                    f_clause_finished(s->f);
                }
                
                skolem_update_satlit(s, (Lit) var_id, new_opposite_sat_lit);
                skolem_update_deterministic(s, var_id, 1);
                skolem_update_pure_neg(s, var_id, 1);
            }
        }
        
        assert(skolem_is_deterministic(s, var_id));
        
        /* Update depencendies and propagation queues before global conflict check,
         * because even when the conflict check is successful, opportunistic
         * CEGAR might handle the conflict, and we then continue propagating.
         */
        skolem_update_dependencies(s, var_id, skolem_compute_dependencies(s,var_id));
        
        // If this pure variable turned out to be constant, update the worklist for constant propagation
        int val = skolem_get_constant_value(s, (Lit) var_id);
        if (val != 0) {
            V3("Pure variable %u gets constant value.\n", var_id);
            s->statistics.pure_constants++;
            skolem_assign_constant_value(s, val * (Lit) var_id, skolem_create_fresh_empty_dep(s), NULL);
        } else {
            // Which clauses may be affected?
            if (s->options->enhanced_pure_literals) {
                skolem_check_occs_for_unique_consequences(s,   (Lit) var_id);
                skolem_check_occs_for_unique_consequences(s, - (Lit) var_id);
            } else {
                if (pure_polarity > 0) {
                    skolem_check_occs_for_unique_consequences(s, - (Lit) var_id);
                } else {
                    skolem_check_occs_for_unique_consequences(s,   (Lit) var_id);
                }
            }
        }
        
        if (locally_conflicted) {
            skolem_global_conflict_check(s, var_id);
            if (skolem_is_conflicted(s)) {
                return;
            }
        }
        
    } else {
        V4("Var %d not pure\n", var_id);
    }
}

unsigned skolem_global_conflict_check(Skolem* s, unsigned var_id) {
    
    if (skolem_is_conflicted(s)) {
        return s->conflict_var_id;
    }
    
    if (s->mode == SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS) {
        return 0;
    }
    
    V3("Global conflit check for var %u.\n", var_id);
    
    double time_stamp_start = get_seconds();
    
    f_push(s->f);
    
    if (s->options->functional_synthesis) {
        for (unsigned i = 0; i < int_vector_count(s->decision_indicator_sat_lits); i++) {
            f_add(s->f, int_vector_get(s->decision_indicator_sat_lits, i));
        }
        f_clause_finished(s->f);
    }
    
    
#ifdef DEBUG
    skolem_var si = skolem_get_info(s, var_id);
    assert(si.pos_lit != - si.neg_lit);
    assert(si.pos_lit != - s->satlit_true);
    assert(si.neg_lit != - s->satlit_true);
#endif
    
    f_add(s->f, skolem_get_satlit(s,   (Lit) var_id));
    f_clause_finished(s->f);
    
    f_add(s->f, skolem_get_satlit(s, - (Lit) var_id));
    f_clause_finished(s->f);
    
    //        satsolver_set_default_phase_lit(s->f, skolem_get_satlit(s,   (Lit) potentially_contflicted), 1);
    //        satsolver_set_default_phase_lit(s->f, skolem_get_satlit(s, - (Lit) potentially_contflicted), 1);
    
    // One of the literals must be true, because the variable is deterministic. Needed for delay-conflict checks. Otherwise we may miss observing some of the conflicts.
    assert(skolem_is_deterministic(s, var_id));
    
    s->statistics.global_conflict_checks++;
    sat_res result = f_sat(s->f);
    
    assert(s->conflict_var_id == 0);
    if (result == SATSOLVER_SATISFIABLE) {
        V3("Conflict!\n");
        
        double time_stamp_end = get_seconds();
        statistic_add_value(s->statistics.global_conflict_checks_sat, time_stamp_end - time_stamp_start);
        
        skolem_bump_conflict_potential(s, var_id);
        
        s->conflict_var_id = var_id;
        
        abortif(s->conflicted_clause != NULL, "Conflicted clause should not be set here.");
        s->state = SKOLEM_STATE_SKOLEM_CONFLICT;
    } else {
        V4("Not conflicted.\n");
        
        double time_stamp_end = get_seconds();
        statistic_add_value(s->statistics.global_conflict_checks_unsat, time_stamp_end - time_stamp_start);
        
        f_pop(s->f);
        
        skolem_slash_conflict_potential(s, var_id);
        
        f_add(s->f, skolem_get_satlit(s,   (Lit) var_id));
        f_add(s->f, skolem_get_satlit(s, - (Lit) var_id));
        f_clause_finished(s->f);
        
        f_add(s->f, - skolem_get_satlit(s,   (Lit) var_id));
        f_add(s->f, - skolem_get_satlit(s, - (Lit) var_id));
        f_clause_finished(s->f);
    }
    
//        f_set_default_phase_lit(s->f, skolem_get_satlit(s,   (Lit) potentially_contflicted), 2);
//        f_set_default_phase_lit(s->f, skolem_get_satlit(s, - (Lit) potentially_contflicted), 2);
    
    return s->conflict_var_id;
}

// BACKTRACKING

void skolem_undo(void* parent, char type, void* obj) {
    Skolem* s = (Skolem*) parent;
    union skolem_undo_union suu;
    suu.ptr = obj;
    skolem_var* si;
    
    switch (type) {

        case SKOLEM_OP_UPDATE_INFO_POS_LIT:
            si = skolem_var_vector_get(s->infos, suu.sus.var_id);
            si->pos_lit = suu.sus.val;
            break;
            
        case SKOLEM_OP_UPDATE_INFO_NEG_LIT:
            si = skolem_var_vector_get(s->infos, suu.sus.var_id);
            si->neg_lit = suu.sus.val;
            break;
            
        case SKOLEM_OP_UPDATE_INFO_DETERMINISTIC:
            si = skolem_var_vector_get(s->infos, suu.sus.var_id);
            if (si->deterministic && (unsigned) suu.sus.val == 0) {
                s->deterministic_variables -= 1;
            }
            si->deterministic = (unsigned) suu.sus.val;
            break;
            
        case SKOLEM_OP_UPDATE_INFO_UNIVERSAL:
            si = skolem_var_vector_get(s->infos, suu.sus.var_id);
            si->universal = (unsigned) suu.sus.val;
            LOG_WARNING("Why would someone temporily set a variable to be universal???");
            break;
            
        case SKOLEM_OP_UPDATE_INFO_PURE_POS:
            si = skolem_var_vector_get(s->infos, suu.sus.var_id);
            si->pure_pos = (unsigned) suu.sus.val;
            break;
            
        case SKOLEM_OP_UPDATE_INFO_PURE_NEG:
            si = skolem_var_vector_get(s->infos, suu.sus.var_id);
            si->pure_neg = (unsigned) suu.sus.val;
            break;
            
        case SKOLEM_OP_UPDATE_INFO_DEPENDENCIES:
            skolem_undo_dependencies(s, obj);
            break;
            
        case SKOLEM_OP_UPDATE_INFO_DECISION_LVL:
            skolem_undo_decision_lvl(s, obj);
            break;
            
        case SKOLEM_OP_UPDATE_INFO_REASON_FOR_CONSTANT:
            skolem_undo_reason_for_constant(s, obj);
            break;
            
        case SKOLEM_OP_UNIQUE_CONSEQUENCE:
            assert(int_vector_count(s->unique_consequence) > (unsigned) obj);
            assert(int_vector_get(s->unique_consequence, (unsigned) obj) != 0);
            UNIQUE_CONSEQUENCE_UNDO_INFO_UNION ucui;
            ucui.data = (int64_t) obj;
            int_vector_set(s->unique_consequence, ucui.components.clause_id, ucui.components.lit);
            break;
            
        case SKOLEM_OP_DECISION:
            s->decision_lvl -= 1;
            if (s->options->functional_synthesis) {
                int_vector_pop(s->decision_indicator_sat_lits);
            }
            break;
            
        default:
            V0("Unknown undo operation in skolem.c: %d\n", (int) type);
            NOT_IMPLEMENTED();
    }
}

void skolem_increase_decision_lvl(Skolem* s) {
    s->decision_lvl += 1;
    stack_push_op(s->stack, SKOLEM_OP_DECISION, NULL);
}

// PRINTING

void skolem_print_statistics(Skolem* s) {
    V0("Skolem statistics:\n");
    V0("  Local determinicity checks: %zu\n",s->statistics.local_determinicity_checks);
    V0("  Local conflict checks: %zu\n",s->statistics.local_conflict_checks);
    V0("  Global conflict checks: %zu\n",s->statistics.global_conflict_checks);
    V0("  Propagations: %zu\n", s->statistics.propagations);
    V0("  Pure variables: %zu\n", s->statistics.pure_vars);
    V0("    of which are constants: %zu\n", s->statistics.pure_constants);
    V0("  Propagations of constants: %zu\n", s->statistics.explicit_propagations);
    V0("  Currently deterministic vars: %zu\n",s->deterministic_variables);
    f_print_statistics(s->f);
    V0("  Histograms for SAT global conflict checks:\n");
    statistics_print(s->statistics.global_conflict_checks_sat);
    V0("  Histograms for UNSAT global conflict checks:\n");
    statistics_print(s->statistics.global_conflict_checks_unsat);
}

void skolem_print_debug_info(Skolem* s) {
    V1("Skolem state\n  Worklist count: %u+%u\n  Stack height: %zu\n  Unique consequences: clause_id -> Lit\n  ", pqueue_count(s->determinicity_queue), pqueue_count(s->pure_var_queue), s->stack->op_count);
    int j = 0;
    for (unsigned i = 0; i < int_vector_count(s->unique_consequence); i++) {
        Lit l = int_vector_get(s->unique_consequence, i);
        if (l != 0) {
            V1("%u -> %d, ",i,l);
            j++;
            if (j % 5 == 4 || i + 1 == int_vector_count(s->unique_consequence)) {
                V1("\n  ");
            }
        }
    }
    V1("\n");
    
    V1("  Nontrivial skolem_vars");
    for (unsigned i = 0; i < skolem_var_vector_count(s->infos); i++) {
        skolem_var si = skolem_get_info(s, i);
        if (si.pos_lit != - s->satlit_true || si.neg_lit != - s->satlit_true) {
            V1("\n  Var %u, det %u, pos %d, neg %d, pure %d, ", i,si.deterministic,si.pos_lit,si.neg_lit, si.pure_neg || si.pure_pos);
            if (s->qcnf->problem_type < QCNF_DQBF) {
                V1("dep_lvl %d\n", si.dep.dependence_lvl);
            } else {
                V1("deps ");
                int_vector_print(si.dep.dependencies);
            }
        }
    }
    V1("\n");
}

////////// CONSTANT PROPAGATION /////////////////

int skolem_get_constant_value(Skolem* s, Lit lit) {
    assert(lit != 0);
    skolem_var sv = skolem_get_info(s, lit_to_var(lit));
    int val = 0;
    assert(sv.pos_lit != s->satlit_true || sv.neg_lit != s->satlit_true);
    if (sv.pos_lit == s->satlit_true) {
        val = 1;
    } else if (sv.neg_lit == s->satlit_true) {
        val = -1;
    }
    if (lit < 0) {
        val = -val;
    }
    assert(val == -1 || val == 0 || val == 1);
    return val;
}

void skolem_update_clause_worklist(Skolem* s, int unassigned_lit) {
    Var* v = var_vector_get(s->qcnf->vars, lit_to_var(unassigned_lit));
    vector* opp_occs = unassigned_lit > 0 ? &v->neg_occs : &v->pos_occs;
    for (unsigned i = 0; i < vector_count(opp_occs); i++) {
        worklist_push(s->clauses_to_check, vector_get(opp_occs, i));
    }
}

// Different from satsolver assumptions. Assume fixes a constant for a variable that is already deterministic
void skolem_assume_constant_value(Skolem* s, Lit lit) {
    V3("Skolem: Assume value %d.\n", lit);
    unsigned var_id = lit_to_var(lit);
    assert(skolem_is_deterministic(s, var_id));
    
    f_add(s->f, skolem_get_satlit(s, lit));
    f_clause_finished(s->f);
    
    union Dependencies deps = skolem_get_dependencies(s, var_id);
    if (s->qcnf->problem_type == QCNF_DQBF) {
        deps.dependencies = int_vector_copy(deps.dependencies);
    }
    
    assert(s->mode == SKOLEM_MODE_STANDARD);
    s->mode = SKOLEM_MODE_CONSTANT_PROPAGATIONS_TO_DETERMINISTICS;
    skolem_assign_constant_value(s, lit, deps, NULL);
    s->mode = SKOLEM_MODE_STANDARD;
    
    // TODO: the assignment might cause many global conflict checks. Suppressing them for variables that are deterministic already seems brutal, but might be OK. If this leads to an inconsistent function definition, no conflicts can be produced in the global conflict check, which is fine in this case. Also, it shouldn't be possible, since we picked a notorious var that had this value already lots of times.
}

// Has the same effect as propagating a singleton clause. May be expensive if called for a deterministic variable, because of required global conflict check.
void skolem_assign_constant_value(Skolem* s, Lit lit, union Dependencies propagation_deps, Clause* reason) {
    // Propagation of constant may be in conflict with existing definitions
    //        assert(!skolem_is_deterministic(s, lit_to_var(lit)));
    assert(lit != 0);
    unsigned var_id = lit_to_var(lit);
    assert(!skolem_is_conflicted(s));
//    assert(skolem_get_satlit(s, lit) != s->satlit_true); // not constant already, not a big problem, but why should this happen?
    abortif(skolem_get_satlit(s, -lit) == s->satlit_true, "Propagation ended in inconsistent state.\n");
    
    V3("Skolem: Assign value %d.\n",lit);
    skolem_update_clause_worklist(s, lit);
    skolem_update_reason_for_constant(s, var_id, reason ? reason->clause_id : INT_MAX, s->decision_lvl);
    
    if (propagation_deps.dependence_lvl == 1) {
        V3("Constant propagation with non-zero dependencies.\n");
    }
    abortif(propagation_deps.dependence_lvl > 0 && s->qcnf->problem_type != QCNF_2QBF, "Propagation of assumptions only supported in 2QBF.\n");
    
    bool was_deterministic_already = skolem_is_deterministic(s, var_id);
    
    if (! skolem_is_deterministic(s, lit_to_var(lit))) {
        skolem_update_decision_lvl(s, var_id, s->decision_lvl);
    }

    bool locally_conflicted = false;
    if (s->mode == SKOLEM_MODE_STANDARD) {
        vector* occs = qcnf_get_occs_of_lit(s->qcnf, -lit);
        for (unsigned i = 0; i < vector_count(occs); i++) {
            Clause* c = vector_get(occs, i);
            if (skolem_get_unique_consequence(s, c) == -lit && ! skolem_clause_satisfied(s, c)) {
                locally_conflicted = true;
                break;
            }
        }
    }
    
    if (locally_conflicted) { // we could alternatively check whether there are clauses with unique consequences for the opposite side.
        V2("Variable %u is assigned a constant but is locally conflicted in the skolem domain.\n", var_id);
        
        if ( ! skolem_is_deterministic(s, lit_to_var(lit))) {
            // We know the variable is deterministic now; it is in fact constant. But we have to add the opposite side of the clauses to be able to do the conflict check
            f_encode_unique_antecedents_for_lits(s, (lit > 0 ? -1 : 1) * (Lit) var_id, false);
        }
        
        skolem_update_satlit(s, lit, s->satlit_true);
        
        skolem_update_deterministic(s, var_id, 1);
    } else {
        skolem_update_satlit(s,   lit,   s->satlit_true);
        skolem_update_satlit(s, - lit, - s->satlit_true);
    }
    
    skolem_update_dependencies(s, var_id, propagation_deps);
    
    if ( ! was_deterministic_already) {
        skolem_update_deterministic(s, var_id, 1);
        skolem_check_occs_for_unique_consequences(s,   (Lit) var_id);
        skolem_check_occs_for_unique_consequences(s, - (Lit) var_id);
    }
    
    /* Checking for conflicts after updating unique consequences for the case that opportunistic CEGAR catches this case.
     *
     */
    if (locally_conflicted) {
        skolem_global_conflict_check(s,var_id);
    }
}

void skolem_propagate_constants_over_clause(Skolem* s, Clause* c) {
    Lit unassigned_lit = 0;
    union Dependencies maximal_deps = skolem_create_fresh_empty_dep(s);
//    union Dependencies universals_max_deps = s->empty_dependencies; // all other dependencies should be larger
    for (int i = 0; i < c->size; i++) {
        int val = skolem_get_constant_value(s, c->occs[i]);
        switch (val) {
            case -1: // this is a (potential) part of the antecedent, need to determine depencence level
                skolem_update_dependencies_for_lit(s, &maximal_deps, c->occs[i]);
                break;
            case 0:
                if (unassigned_lit != 0) {
                    // two unassigned existentials; clause cannot propagate
                    goto cleanup;
                } else {
                    unassigned_lit = c->occs[i];
                }
                break;
            case 1:
                goto cleanup; // clause satisfied
//            default: // cannot happen
//                abort();
        }
    }
    if (s->qcnf->problem_type == QCNF_DQBF) {
        maximal_deps.dependencies = int_vector_copy(maximal_deps.dependencies); // have to copy the set
    }
    
    //    VAL new_val = top;
    if (unassigned_lit == 0) { // conflict
        assert(!skolem_is_conflicted(s));
        s->statistics.explicit_propagation_conflicts++;
        s->conflicted_clause = c;
        s->conflict_var_id = lit_to_var(c->occs[c->size - 1]); // conflict is the last variable in the clause :/
        s->state = SKOLEM_STATE_CONSTANTS_CONLICT;
        
        V3("Conflict in explicit propagation in skolem domain for clause %u and var %u\n", s->conflicted_clause->clause_id, s->conflict_var_id);
        
    } else { // assign value
        if ((qcnf_is_universal(s->qcnf, lit_to_var(unassigned_lit)) ||
                skolem_is_initially_deterministic(s, lit_to_var(unassigned_lit)) ) &&
            s->mode != SKOLEM_MODE_CONSTANT_PROPAGATIONS_TO_DETERMINISTICS) {
            
            goto cleanup;
        }
        
//         V4("Propagating variable %d.\n",unassigned_lit);
        s->statistics.propagations += 1;
        s->statistics.explicit_propagations += 1;
        
        assert(skolem_get_unique_consequence(s, c) != 0);
        
        skolem_assign_constant_value(s, unassigned_lit, maximal_deps, c);
    }
cleanup:
    if (s->qcnf->problem_type == QCNF_DQBF) {
        int_vector_free(maximal_deps.dependencies);
    }
}

// fixes the __remaining__ cases to be value
void skolem_decision(Skolem* s, Lit decision_lit) {
    assert(!skolem_can_propagate(s));
    
    V3("Decision %d, new dlvl is %u\n", decision_lit, s->decision_lvl + 1);
    unsigned decision_var_id = lit_to_var(decision_lit);
    
    assert(skolem_get_decision_lvl(s, decision_var_id) == 0);
    assert(!skolem_is_deterministic(s, decision_var_id));
    assert(skolem_get_constant_value(s, decision_lit) == 0);
    
    // Increase decision level, set
    skolem_increase_decision_lvl(s);
    skolem_update_decision_lvl(s, decision_var_id, s->decision_lvl);
    
    /* Tricky bug: In case the decision var is conflicted and both lits are true, the definitions below
     * allowed the decision var to be set only to one value. For a conflict check over the decision var
     * only that's not a problem, but it is a problem if the check gets delayed, multiple variables are
     * checked at the same time, and a later variable is determined to be conflicted even though for
     * the same input the decision var would be conflicted as well.
     */
    bool positive_side_needs_complete_definitions_too = s->options->functional_synthesis;
    
    f_encode_unique_antecedents_for_lits(s,  decision_lit, positive_side_needs_complete_definitions_too);
    bool opposite_case_exists = f_encode_unique_antecedents_for_lits(s, - decision_lit, true);
    
    // Here we already fix the function domain decisions
    // This is a precautionary measure to prevent conflict analysis from interpreting the decision as a
    // reason for setting the decision_var to value in cases where there should also be a different reason. Decision
    // can only be taken as a reason when -opposite_satlit.
    Lit val_satlit =      skolem_get_satlit(s,   decision_lit);
    Lit opposite_satlit = skolem_get_satlit(s, - decision_lit);
    
    // define:  new_val_satlit := (val_satlit || - opposite_satlit)
    int new_val_satlit = f_fresh_var(s->f);
    
    // first clause: new_val_satlit => (val_satlit || - opposite_satlit)
    f_add(s->f, - new_val_satlit);
    f_add(s->f, val_satlit);
    f_add(s->f, - opposite_satlit);
    f_clause_finished(s->f);
    
    // second and third clause: (val_satlit || - opposite_satlit) => new_val_satlit
    f_add(s->f, - val_satlit);
    f_add(s->f, new_val_satlit);
    f_clause_finished(s->f);
    
    f_add(s->f, opposite_satlit);
    f_add(s->f, new_val_satlit);
    f_clause_finished(s->f);
    
    skolem_update_satlit(s, decision_lit, new_val_satlit);
    
    skolem_update_deterministic(s, decision_var_id, 1);
    
    skolem_var si = skolem_get_info(s, decision_var_id);
    union Dependencies new_deps = skolem_copy_dependencies(s, si.dep);
    skolem_update_dependencies(s, decision_var_id, new_deps);
    
    if (s->options->functional_synthesis) {
        // For functional synthesis, we will require that all conflicts involve at least one decision var. For that we introduce a sat_lit that represents exactly that.
        
        // Define the sat_lit_fresh := new_val_satlit && -val_satlit  // - opposite_satlit && - val_satlit
        int sat_lit_fresh = f_fresh_var(s->f);
        
        int_vector_add(s->decision_indicator_sat_lits, sat_lit_fresh);

        f_add(s->f, sat_lit_fresh);
        f_add(s->f, - new_val_satlit);
        f_add(s->f,   val_satlit);
        f_clause_finished(s->f);
        
        f_add(s->f, - sat_lit_fresh);
        f_add(s->f,   new_val_satlit);
        f_clause_finished(s->f);
        
        f_add(s->f, - sat_lit_fresh);
        f_add(s->f, - val_satlit);
        f_clause_finished(s->f);
    }
    
    skolem_check_occs_for_unique_consequences(s,   (Lit) decision_var_id);
    skolem_check_occs_for_unique_consequences(s, - (Lit) decision_var_id);
    
    // Decision variable needs to be deterministic before we can do conflict checks. Also this is why we have to check exactly here.
    if (skolem_is_locally_conflicted(s, decision_var_id)) {
        skolem_global_conflict_check(s, decision_var_id);
        if (skolem_is_conflicted(s)) {
            V2("Decision variable %d is conflicted, going into conflict analysis instead.\n", decision_var_id);
            return;
        }
    }
    
    // Determine whether we decide on a value or a function
    bool value_decision = ! opposite_case_exists;
    
    if (value_decision) {
        V3("Value decision for var %u\n", decision_var_id);
        assert(opposite_satlit == - s->satlit_true);
        skolem_assign_constant_value(s, decision_lit, s->empty_dependencies, NULL);
    }
}


void skolem_propagate(Skolem* s) {
    V3("Propagating in Skolem domain\n");
    while (worklist_count(s->clauses_to_check) || pqueue_count(s->determinicity_queue) || pqueue_count(s->pure_var_queue)) {
        if (skolem_is_conflicted(s)) {
            V4("Skolem domain is in conflict state; stopping propagation.\n");
            break;
        }
        
        if (worklist_count(s->clauses_to_check)) {
            Clause* c = worklist_pop(s->clauses_to_check);
            skolem_propagate_constants_over_clause(s, c);
        } else if (pqueue_count(s->determinicity_queue)) {
            unsigned var_id = (unsigned) pqueue_pop(s->determinicity_queue);
            skolem_propagate_determinicity(s, var_id);
        } else if (pqueue_count(s->pure_var_queue)) {
            unsigned var_id = (unsigned) pqueue_pop(s->pure_var_queue);
            skolem_propagate_pure_variable(s, var_id);
        }
    }
    assert( ! skolem_can_propagate(s) || skolem_is_conflicted(s));
}
