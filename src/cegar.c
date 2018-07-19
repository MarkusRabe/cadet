//
//  cegar.c
//  cadet
//
//  Created by Markus Rabe on 08.02.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "cadet_internal.h"
#include "casesplits.h"
#include "log.h"

#include <assert.h>

bool cegar_var_needs_to_be_set(Casesplits* cs, unsigned var_id) {
    abortif(int_vector_get(cs->is_used_in_lemma, var_id) == 0, "Variable not used in CEGAR lemma?");
    int satval = satsolver_deref(cs->exists_solver, (int) var_id);
    abortif(satval == 0, "CEGAR lemma variable not set in SAT solver");
    
    Var* v = var_vector_get(cs->skolem->qcnf->vars, var_id);
    vector* occs = satval > 0 ? &v->pos_occs : &v->neg_occs;
    int_vector* additional_assignments_var = int_vector_init();
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        if (! c->original || c->blocked) {
            continue;
        }
        bool c_satisfied_without = false;
        int can_be_satisfied_by_unset = 0;
        for (unsigned j = 0; j < c->size; j++) {
            int occ = c->occs[j];
            if (var_id == lit_to_var(occ)) {
                continue;
            }
            if (satsolver_deref(cs->exists_solver, occ) == -1 || int_vector_get(cs->is_used_in_lemma, lit_to_var(occ)) == 0) {
                continue;
            }
            
            if (satsolver_deref(cs->exists_solver, occ) == 1 || int_vector_contains_sorted(cs->additional_assignment, occ) || int_vector_contains_sorted(additional_assignments_var, occ)) {
                c_satisfied_without = true;
                break;
            } else {
                assert(satsolver_deref(cs->exists_solver, occ) == 0);
                if (can_be_satisfied_by_unset == 0 && ! int_vector_contains_sorted(cs->additional_assignment, -occ) && ! int_vector_contains_sorted(additional_assignments_var, - occ)) {
                    c_satisfied_without = true;
                    can_be_satisfied_by_unset = occ;
                }
            }
        }
        
        if (!c_satisfied_without) {
            int_vector_free(additional_assignments_var);
            return true;
        }
        if (can_be_satisfied_by_unset != 0) {
            cs->cegar_stats.additional_assignments_num += 1;
            int_vector_add_sorted(additional_assignments_var, can_be_satisfied_by_unset);
        }
    }
    int_vector_add_all_sorted(cs->additional_assignment, additional_assignments_var);
    if (int_vector_count(additional_assignments_var) > 0) {
        cs->cegar_stats.successful_minimizations_by_additional_assignments += 1;
    }
    int_vector_free(additional_assignments_var);
    cs->cegar_stats.successful_minimizations += 1;
    return false;
}

void cegar_one_round_for_conflicting_assignment(C2* c2) {
    assert(casesplits_is_initialized(c2->cs));
    assert(c2->state == C2_SKOLEM_CONFLICT);
    Casesplits* cs = c2->cs;
    
    V3("Assuming: ");
    for (unsigned i = 0 ; i < int_vector_count(cs->interface_vars); i++) {
        unsigned var_id = (unsigned) int_vector_get(cs->interface_vars, i);
        int_vector_set(cs->is_used_in_lemma, var_id, 1); // reset values
        
        int val = cegar_get_val(c2->skolem, (int) var_id);
        satsolver_assume(cs->exists_solver, val * (Lit) var_id);
        V3(" %d", val * (Lit) var_id);
    }
    V3("\n");
    
#ifdef DEBUG
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (!v->original) {
            continue;
        }
        assert(int_vector_get(cs->is_used_in_lemma, i) == 1);
    }
#endif
    
    if (satsolver_sat(cs->exists_solver) == SATSOLVER_SAT) {
        int_vector_reset(cs->additional_assignment);
        
        int_vector* cube = int_vector_init();
        for (unsigned i = 0 ; i < int_vector_count(cs->interface_vars); i++) {
            unsigned var_id = (unsigned) int_vector_get(cs->interface_vars, i);
            if (cegar_var_needs_to_be_set(cs, var_id)) {
                int val = satsolver_deref(cs->exists_solver, (Lit) var_id);
                Lit lit = val * (Lit) var_id;
                int_vector_add(cube, lit);
            } else {
                int_vector_set(cs->is_used_in_lemma, var_id, 0);
            }
        }
        
        int_vector* existentials = NULL;
        if (c2->options->certify_SAT) {
            existentials = int_vector_init();
            for (unsigned var_id = 1; var_id < var_vector_count(c2->qcnf->vars); var_id++) {
                if (!qcnf_var_exists(c2->qcnf, var_id)) {
                    continue;
                }
                if (! skolem_is_deterministic(c2->skolem, var_id) || skolem_get_decision_lvl(c2->skolem, var_id) > 0) {
                    int val = satsolver_deref(cs->exists_solver, (int) var_id);
                    if (val == 0) {
                        if (int_vector_find_sorted(cs->additional_assignment, - (int) var_id)) {
                            val = -1;
                        } else { // potentially (int) var_id is in additional_assignment
                            val = +1;  // default is +1
                        }
                    }
                    assert(val == -1 || val == +1);
                    int_vector_add(existentials, val * (int) var_id);
                }
            }
        }
        casesplits_record_cegar_cube(c2->cs, cube, existentials);
        casesplits_encode_CEGAR_case(c2->cs);
        c2->cs->cegar_stats.recent_average_cube_size = (float) int_vector_count(cube) * (float) 0.1 + c2->cs->cegar_stats.recent_average_cube_size * (float) 0.9;
    } else {
        if (c2->options->functional_synthesis) {
            int_vector* core = int_vector_init();
            satsolver_failed_assumptions(cs->exists_solver, core);
            for (unsigned i = 0; i < int_vector_count(core); i++) {
                Lit lit = int_vector_get(core, i);
//                qcnf_add_lit(c2->qcnf, - lit);
                int satlit = skolem_get_satsolver_lit(c2->skolem, lit);
                satsolver_add(c2->skolem->skolem, - satlit);
            }
            satsolver_clause_finished_for_context(c2->skolem->skolem, 0);
//            Clause* c = qcnf_close_clause(c2->qcnf);
//            abortif(!c, "Could not create clause from unsat core in functional synthesis cegar iteration.");
//            c->original = 0;
//            c->consistent_with_originals = 0;
//            c->is_cube = 1;
//            c2_new_clause(c2, c);
            
            int_vector_free(core);
            return;
        }
        
        c2->state = C2_UNSAT;
    }
    return;
}

void cegar_solve_2QBF_by_cegar(C2* c2, int rounds_num) {
    assert(c2->state == C2_READY);
    assert(casesplits_is_initialized(c2->cs));
    
    // solver loop
    while (c2->state == C2_READY && rounds_num--) {
        if (!skolem_check_if_domain_is_empty(c2->skolem)) {
            cegar_one_round_for_conflicting_assignment(c2);
        } else {
            c2->state = C2_SAT;
            break; // skolem is in 'complete' state
        }
    }
    return;
}

int cegar_get_val(void* domain, Lit lit) {
    Skolem* s = (Skolem*) domain;
    int val = skolem_get_value_for_conflict_analysis(s, lit);
    if (val == 0) {
        val = 1;
    }
    assert(val == -1 || val == 1);
    return val;
}

