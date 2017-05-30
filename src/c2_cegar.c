//
//  c2_cegar.c
//  cadet
//
//  Created by Markus Rabe on 28/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "c2_cegar.h"
#include "log.h"


Cegar* cegar_init(QCNF* qcnf) {
    Cegar* cegar = malloc(sizeof(Cegar));
    cegar->qcnf = qcnf;
    cegar->additional_assignment = int_vector_init();
    cegar->solved_cubes = vector_init();
    cegar->exists_solver = NULL; // no initialized yet; see cegar_update_interface
    cegar->interface_vars = NULL;
    
    // Magic values
    cegar->cegar_effectiveness_threshold = 20;
    
    // Statistics
    cegar->successful_minimizations = 0;
    cegar->additional_assignments_num = 0;
    cegar->successful_minimizations_by_additional_assignments = 0;
    cegar->cubes_num = 0;
    cegar->recent_average_cube_size = 0;
    
    
    cegar->is_used_in_lemma = int_vector_init();
    // initialize vector of bits saying we need this variable in the blocking clause
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        int_vector_add(cegar->is_used_in_lemma, 1);
    }
    
    return cegar;
}

bool cegar_is_initialized(Cegar* cegar) {
    return cegar->interface_vars;
}

void cegar_update_interface(Skolem* s) {
    
    Cegar* cegar = s->cegar;
    
    const unsigned max_var_id = var_vector_count(cegar->qcnf->vars);
    cegar->exists_solver = satsolver_init();
    satsolver_set_max_var(cegar->exists_solver, (int) max_var_id);
    
    // set up satsolver for existentials
    for (unsigned i = 0; i < vector_count(s->qcnf->clauses); i++) {
        Clause* c = vector_get(s->qcnf->clauses, i);
        if (!c) {
            continue;
        }
        unsigned uc_var = lit_to_var(skolem_get_unique_consequence(s, c));
        if (uc_var != 0 && skolem_is_deterministic(s, uc_var)) {
            continue;
        }
        for (unsigned j = 0; j < c->size; j++) {
            assert(lit_to_var(c->occs[j]) < max_var_id);
            satsolver_add(cegar->exists_solver, c->occs[j]);
        }
        satsolver_clause_finished(cegar->exists_solver);
    }
    
    // determine interface variables; variables that are deterministic and occur in clauses together with nondeterministic variables.
    int_vector* old_interface = cegar->interface_vars;
    cegar->interface_vars = int_vector_init();
    for (unsigned i = 0; i < vector_count(s->qcnf->clauses); i++) {
        Clause* c = vector_get(s->qcnf->clauses, i);
        if (!c) {
            continue;
        }
        unsigned uc_var = lit_to_var(skolem_get_unique_consequence(s, c));
        if (uc_var != 0 && skolem_is_deterministic(s, uc_var)) {
            continue;
        }
        for (unsigned j = 0; j < c->size; j++) {
            if (skolem_is_deterministic(s, lit_to_var(c->occs[j]))) {
                int_vector_add(cegar->interface_vars, (int) lit_to_var(c->occs[j]));
            }
        }
    }
    
    int_vector_sort(cegar->interface_vars, compare_integers_natural_order);
    int_vector_remove_duplicates(cegar->interface_vars);
    
    if (debug_verbosity >= VERBOSITY_LOW) {
        V1("Interface vars:  ");
        int_vector_print(cegar->interface_vars);
        V1("\n");
    }
    
    // Interface should only extend; otherwise the cubes in solved_cubes may refer to non-deterministic variables
    if (debug_verbosity >= VERBOSITY_HIGH && old_interface != NULL) {
        for (unsigned i = 0; i < int_vector_count(old_interface); i++) {
            assert(int_vector_contains(cegar->interface_vars, int_vector_get(old_interface, i)));
        }
    }
    free(old_interface);
}

bool cegar_var_needs_to_be_set(Cegar* cegar, unsigned var_id) {
    abortif(int_vector_get(cegar->is_used_in_lemma, var_id) == 0, "Variable not used in CEGAR lemma?");
    int satval = satsolver_deref(cegar->exists_solver, (int) var_id);
    abortif(satval == 0, "CEGAR lemma variable not set in SAT solver");
    
    Var* v = var_vector_get(cegar->qcnf->vars, var_id);
    vector* occs = satval > 0 ? &v->pos_occs : &v->neg_occs;
    int_vector* additional_assignments_var = int_vector_init();
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        bool c_satisfied_without = false;
        int can_be_satisfied_by_unset = 0;
        for (unsigned j = 0; j < c->size; j++) {
            int occ = c->occs[j];
            if (var_id == lit_to_var(occ)) {
                continue;
            }
            if (satsolver_deref(cegar->exists_solver, occ) == -1 || int_vector_get(cegar->is_used_in_lemma, lit_to_var(occ)) == 0) {
                continue;
            }
            
            if (satsolver_deref(cegar->exists_solver, occ) == 1 || int_vector_contains_sorted(cegar->additional_assignment, occ) || int_vector_contains_sorted(additional_assignments_var, occ)) {
                c_satisfied_without = true;
                break;
            } else {
                assert(satsolver_deref(cegar->exists_solver, occ) == 0);
                if (can_be_satisfied_by_unset == 0 && ! int_vector_contains_sorted(cegar->additional_assignment, -occ) && ! int_vector_contains_sorted(additional_assignments_var, - occ)) {
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
            cegar->additional_assignments_num += 1;
            int_vector_add_sorted(additional_assignments_var, can_be_satisfied_by_unset);
        }
    }
    int_vector_add_all_sorted(cegar->additional_assignment, additional_assignments_var);
    if (int_vector_count(additional_assignments_var) > 0) {
        cegar->successful_minimizations_by_additional_assignments += 1;
    }
    int_vector_free(additional_assignments_var);
    cegar->successful_minimizations += 1;
    return false;
}

void cegar_free(Cegar* c) {
    satsolver_free(c->exists_solver);
    int_vector_free(c->interface_vars);
    int_vector_free(c->is_used_in_lemma);
    for (unsigned i = 0; i < vector_count(c->solved_cubes); i++) {
        int_vector_free((int_vector*)vector_get(c->solved_cubes, i));
    }
    vector_free(c->solved_cubes);
}

cadet_res cegar_solve_2QBF(C2* c2, int rounds_num) {
    
    assert(cegar_is_initialized(c2->skolem->cegar));
    
    // solver loop
    while (c2->result == CADET_RESULT_UNKNOWN && rounds_num--) {
        if (satsolver_sat(c2->skolem->skolem) == SATSOLVER_RESULT_SAT) {
            cegar_build_abstraction_for_assignment(c2);
        } else {
            c2->result = CADET_RESULT_SAT;
        }
    }
    return c2->result;
}

void cegar_do_cegar_if_effective(C2* c2) {
    assert(cegar_is_initialized(c2->skolem->cegar));
    unsigned i = 0;
    while (c2->result == CADET_RESULT_UNKNOWN &&
           c2->skolem->cegar->recent_average_cube_size < c2->skolem->cegar->cegar_effectiveness_threshold) {
        i++;
        cegar_solve_2QBF(c2,1);
    }
    V1("Executed %u rounds of CEGAR.\n", i);
    if (c2->result == CADET_RESULT_UNKNOWN) {
        V1("CEGAR inconclusive, returning to normal mode.\n");
    } else {
        V1("CEGAR solved the problem: %d\n", c2->result);
    }
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

cadet_res cegar_build_abstraction_for_assignment(C2* c2) {
    assert(cegar_is_initialized(c2->skolem->cegar));
    assert(c2->result == CADET_RESULT_UNKNOWN);
    Cegar* cegar = c2->skolem->cegar;
    
    V3("Assuming: ");
    for (unsigned i = 0 ; i < int_vector_count(cegar->interface_vars); i++) {
        unsigned var_id = (unsigned) int_vector_get(cegar->interface_vars, i);
        int_vector_set(cegar->is_used_in_lemma, var_id, 1); // reset values
        
        int val = cegar_get_val(c2->skolem, (int) var_id);
        satsolver_assume(cegar->exists_solver, val * (Lit) var_id);
        V3(" %d", val * (Lit) var_id);
    }
    V3("\n");
    
#ifdef DEBUG
    for (unsigned i = 0; i < var_vector_count(c2->qcnf->vars); i++) {
        Var* v = var_vector_get(c2->qcnf->vars, i);
        if (!v->original) {
            continue;
        }
        assert(int_vector_get(cegar->is_used_in_lemma, i) == 1);
    }
#endif
    
    if (satsolver_sat(cegar->exists_solver) == SATSOLVER_RESULT_SAT) {
        
        V1("CEGAR adding clause: ");
        int_vector_reset(cegar->additional_assignment);
        int_vector* cube = int_vector_init();
        
        for (unsigned i = 0 ; i < int_vector_count(cegar->interface_vars); i++) {
            unsigned var_id = (unsigned) int_vector_get(cegar->interface_vars, i);
            int val = satsolver_deref(cegar->exists_solver, (int) var_id);
            
            if (cegar_var_needs_to_be_set(cegar, var_id)) {
                Lit lit = - val * (Lit) var_id;
                V3("%d ", lit);
                int_vector_add(cube, lit);
                int satlit = skolem_get_satsolver_lit(c2->skolem, lit);
                satsolver_add(c2->skolem->skolem, satlit);
            } else {
                int_vector_set(cegar->is_used_in_lemma, var_id, 0);
            }
        }
        satsolver_clause_finished_for_context(c2->skolem->skolem, 0);
        
        V1(" ... length %u\n", int_vector_count(cube));
        vector_add(cegar->solved_cubes, cube);
        
        cegar->cubes_num += 1;
        cegar->recent_average_cube_size = (float) int_vector_count(cube) * (float) 0.1 + cegar->recent_average_cube_size * (float) 0.9;
    } else {
        c2->state = C2_CEGAR_CONFLICT;
        c2->result = CADET_RESULT_UNSAT;
    }
    return c2->result;
}


bool cegar_try_to_handle_conflict(Skolem* s) {
    assert(cegar_is_initialized(s->cegar));
    Cegar* cegar = s->cegar;
    
    V3("Assuming: ");
    for (unsigned i = 0 ; i < int_vector_count(cegar->interface_vars); i++) {
        unsigned var_id = (unsigned) int_vector_get(cegar->interface_vars, i);
        int_vector_set(cegar->is_used_in_lemma, var_id, 1); // reset values
        
        int val = cegar_get_val(s, (int) var_id);
        satsolver_assume(cegar->exists_solver, val * (Lit) var_id);
        V3(" %d", val * (Lit) var_id);
    }
    V3("\n");
    
#ifdef DEBUG
    for (unsigned i = 0; i < var_vector_count(s->qcnf->vars); i++) {
        Var* v = var_vector_get(s->qcnf->vars, i);
        if (!v->original) {
            continue;
        }
        assert(int_vector_get(cegar->is_used_in_lemma, i) == 1);
    }
#endif
    
    if (satsolver_sat(cegar->exists_solver) == SATSOLVER_RESULT_SAT) {
        
        V1("CEGAR adding clause (inplace): ");
        int_vector_reset(cegar->additional_assignment);
        int_vector* cube = int_vector_init();
        

        for (unsigned i = 0 ; i < int_vector_count(cegar->interface_vars); i++) {
            unsigned var_id = (unsigned) int_vector_get(cegar->interface_vars, i);
            int val = satsolver_deref(cegar->exists_solver, (int) var_id);
            
            if (cegar_var_needs_to_be_set(cegar, var_id)) {
                Lit lit = - val * (Lit) var_id;
                V3("%d ", lit);
                int_vector_add(cube, lit);
            } else {
                int_vector_set(cegar->is_used_in_lemma, var_id, 0);
            }
        }
        
        V1(" ... length %u\n", int_vector_count(cube));
        
        vector_add(cegar->solved_cubes, cube);
        
        for (unsigned i = 0 ; i < int_vector_count(cube); i++) {
            int lit = int_vector_get(cube, i);
            int satlit = skolem_get_satsolver_lit(s, lit);
            satsolver_add(s->skolem, satlit);
        }
        satsolver_clause_finished_for_context(s->skolem, 0);
        
        cegar->cubes_num += 1;
        cegar->recent_average_cube_size = (float) int_vector_count(cube) * (float) 0.1 + cegar->recent_average_cube_size * (float) 0.9;
        
        if ((float) int_vector_count(cube) < cegar->cegar_effectiveness_threshold) {
            return true;
        } else {
            return false;
        }
    } else {
        // We found an actual conflict; returning false will let conflict analysis proceed, including later CEGAR check.
        V1("Found an actual conflict, but let the outer CEGAR check discover this again.\n");
        return false;
    }
}

void cegar_print_statistics(Cegar* cegar) {
    if (cegar && cegar_is_initialized(cegar)) {
        V0("Cegar statistics:\n");
        V0("  Interface size: %u\n", int_vector_count(cegar->interface_vars));
        V0("  Number of cubes: %u\n", cegar->cubes_num);
        V0("  Successful minimizations: %u\n", cegar->successful_minimizations);
        V0("  Additional assignments: %u\n", cegar->additional_assignments_num);
        V0("  Additional assignments helped: %u\n", cegar->successful_minimizations_by_additional_assignments);
    }
}
