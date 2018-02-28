//
//  casesplits.c
//  cadet
//
//  Created by Markus Rabe on 28/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "casesplits.h"
#include "log.h"

#include <math.h>

Casesplits* casesplits_init(QCNF* qcnf, Options* options) {
    Casesplits* d = malloc(sizeof(Casesplits));
    d->qcnf = qcnf;
    d->skolem = NULL;
    d->options = options;
    d->solved_cases = vector_init();
    
    d->interface_vars = NULL;
    d->interface_activities = float_vector_init();
    d->original_satlits = map_init();
    
    // CEGAR
    d->exists_solver = NULL; // no initialized yet; see domain_update_interface
    d->additional_assignment = int_vector_init();
    d->is_used_in_lemma = int_vector_init();
    // CEGAR statistics
    d->cegar_stats.successful_minimizations = 0;
    d->cegar_stats.additional_assignments_num = 0;
    d->cegar_stats.successful_minimizations_by_additional_assignments = 0;
    d->cegar_stats.recent_average_cube_size = 0;
    d->cegar_magic.max_cegar_iterations_per_learnt_clause = 50;
    d->cegar_magic.cegar_effectiveness_threshold = 17;
    d->cegar_magic.universal_activity_decay = (float) 0.95;
    
    // initialize vector of bits saying we need this variable in the blocking clause
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        int_vector_add(d->is_used_in_lemma, 1);
    }
    
    return d;
}

bool casesplits_is_initialized(Casesplits* cs) {
    return cs->interface_vars != NULL;
}

float casesplits_get_interface_activity(Casesplits* cs, unsigned var_id) {
    if (float_vector_count(cs->interface_activities) > var_id) {
        return float_vector_get(cs->interface_activities, var_id);
    } else {
        return (float) 0.0;
    }
}
void casesplits_add_interface_activity(Casesplits* cs, unsigned var_id, float value) {
    while (float_vector_count(cs->interface_activities) <= var_id) {
        float_vector_add(cs->interface_activities, (float) 0.0);
    }
    float old = float_vector_get(cs->interface_activities, var_id);
    float_vector_set(cs->interface_activities, var_id, old + value);
}
void casesplits_decay_interface_activity(Casesplits* d, unsigned var_id) {
//    for (unsigned i = 0; i < float_vector_count(cegar->interface_activities); i++) {
    if (var_id >= float_vector_count(d->interface_activities)) {
        return;
    }
    float old = float_vector_get(d->interface_activities, var_id);
    float_vector_set(d->interface_activities, var_id, old * d->cegar_magic.universal_activity_decay);
//    }
}

void cegar_remember_original_satlit(Casesplits* cs, unsigned var_id) {
    assert(skolem_is_deterministic(cs->skolem, var_id));
    assert(cs->skolem->stack->push_count == 0);
    int satlit_pos = skolem_get_satsolver_lit(cs->skolem,   (Lit) var_id);
    int satlit_neg = skolem_get_satsolver_lit(cs->skolem, - (Lit) var_id);
    map_add(cs->original_satlits,   (Lit) var_id, (void*) (long) satlit_pos);
    map_add(cs->original_satlits, - (Lit) var_id, (void*) (long) satlit_neg);
}

void casesplits_update_interface(Casesplits* cs, Skolem* skolem) {
    assert(cs->skolem == NULL || cs->skolem == skolem);
    cs->skolem = skolem;
    
    if (cs->exists_solver) {satsolver_free(cs->exists_solver);}
    cs->exists_solver = satsolver_init();
    
    const unsigned max_var_id = var_vector_count(cs->qcnf->vars);
    satsolver_set_max_var(cs->exists_solver, (int) max_var_id);
    
    // set up satsolver for existentials
    for (unsigned i = 0; i < vector_count(cs->qcnf->clauses); i++) {
        Clause* c = vector_get(cs->qcnf->clauses, i);
        if (!c || ! c->original) {
            continue;
        }
        unsigned uc_var = lit_to_var(skolem_get_unique_consequence(cs->skolem, c));
        if (uc_var != 0 && skolem_is_deterministic(cs->skolem, uc_var)) {
            continue;
        }
        for (unsigned j = 0; j < c->size; j++) {
            assert(lit_to_var(c->occs[j]) < max_var_id);
            satsolver_add(cs->exists_solver, c->occs[j]);
        }
        satsolver_clause_finished(cs->exists_solver);
    }
    
    // determine interface variables; variables that are deterministic and occur in clauses together with nondeterministic variables.
    int_vector* old_interface = cs->interface_vars;
    cs->interface_vars = int_vector_init();
    for (unsigned i = 0; i < vector_count(cs->qcnf->clauses); i++) {
        Clause* c = vector_get(cs->qcnf->clauses, i);
        if (!c || ! c->original || c->blocked) {
            continue;
        }
        unsigned uc_var = lit_to_var(skolem_get_unique_consequence(cs->skolem, c));
        if (uc_var != 0 && skolem_is_deterministic(cs->skolem, uc_var)) {
            continue;
        }
        for (unsigned j = 0; j < c->size; j++) {
            if (skolem_is_deterministic(cs->skolem, lit_to_var(c->occs[j]))) {
                int_vector_add(cs->interface_vars, (int) lit_to_var(c->occs[j]));
            }
        }
    }
    
    int_vector_sort(cs->interface_vars, compare_integers_natural_order);
    int_vector_remove_duplicates(cs->interface_vars);
    
    for (unsigned i = 0; i < int_vector_count(cs->interface_vars); i++) {
        Lit interface_lit = int_vector_get(cs->interface_vars, i);
        assert(interface_lit > 0); // not required for correctness, just a sanity check
        unsigned interface_var = lit_to_var(interface_lit);
        cegar_remember_original_satlit(cs, interface_var);
    }
    
    V1("Deterministic vars: %u\n", int_vector_count(cs->skolem->determinization_order));
    V1("Interface vars: (%u in total) ... ", int_vector_count(cs->interface_vars));
    if (debug_verbosity >= VERBOSITY_HIGH || (debug_verbosity >= VERBOSITY_LOW && int_vector_count(cs->interface_vars) < 20)) {
        int_vector_print(cs->interface_vars);
    }
    V1("\n");
    
    // Interface should only extend; otherwise the cubes in solved_cubes may refer to non-deterministic variables
    if (old_interface != NULL) {
        if (debug_verbosity >= VERBOSITY_HIGH) {
            for (unsigned i = 0; i < int_vector_count(old_interface); i++) {
                assert(int_vector_contains(cs->interface_vars, int_vector_get(old_interface, i)));
            }
        }
        free(old_interface);
    }
}

void case_free(Case* c) {
    if (c->universal_assumptions) {int_vector_free(c->universal_assumptions);}
    if (c->decisions) {int_vector_free(c->decisions);}
    if (c->qcnf) {qcnf_free(c->qcnf);}
    free(c);
}

void casesplits_free(Casesplits* d) {
    if (d->exists_solver) {satsolver_free(d->exists_solver);}
    if (d->interface_vars) {int_vector_free(d->interface_vars);}
    if (d->interface_activities) {float_vector_free(d->interface_activities);}
    if (d->original_satlits) {map_free(d->original_satlits);}
    int_vector_free(d->is_used_in_lemma);
    for (unsigned i = 0; i < vector_count(d->solved_cases); i++) {
        case_free((Case*) vector_get(d->solved_cases, i));
    }
    vector_free(d->solved_cases);
}


Case* case_init() {
    Case* c = malloc(sizeof(Case));
    c->type = 0;
    c->universal_assumptions = NULL;
    c->decisions = NULL;
    c->qcnf = NULL;
    return c;
}

void casesplits_close_heuristics(Casesplits* cs, int_vector* solved_cube) {
    if (int_vector_count(solved_cube) < 20) { // prevent tinitiny increments, NaN-hell, etc
        float activity_bump = (float) ((double) 1.0 / pow(2.0, (double) int_vector_count(solved_cube)));
        //        float activity_bump = (float) ((double) 1.0 / (double) (c2->case_split_depth * c2->case_split_depth + 1.0));
        V1("Activity bump: %f\n", activity_bump);
        for (unsigned i = 0; i < int_vector_count(solved_cube); i++) {
            unsigned var_id = lit_to_var(int_vector_get(solved_cube, i));
            casesplits_add_interface_activity(cs, var_id, activity_bump);
        }
    }
}

void casesplits_encode_last_case(Casesplits* cs) {
    Case* c = vector_get(cs->solved_cases, vector_count(cs->solved_cases) - 1);
    if (c->type == 0 || (c->type == 1 && cs->options->casesplits_cubes)) { // cube case
        for (unsigned i = 0; i < int_vector_count(c->universal_assumptions); i++) {
            Lit lit = int_vector_get(c->universal_assumptions, i);
            assert(skolem_is_deterministic(cs->skolem, lit_to_var(lit)));
            assert(skolem_get_decision_lvl(cs->skolem, lit_to_var(lit)) == 0);
            assert(map_contains(cs->original_satlits, - lit));
            int satlit = (int) (long) map_get(cs->original_satlits, - lit);
            //        int satlit = skolem_get_satsolver_lit(s, lit); // doesn't work, as the universal variables could be updated to be constant after case split assumptions
            satsolver_add(cs->skolem->skolem, satlit);
        }
        satsolver_clause_finished_for_context(cs->skolem->skolem, 0);
    } else { // function case
        assert(c->type == 1);
        Skolem* encoding_skolem = skolem_init(c->qcnf, cs->options);
        encoding_skolem->record_conflicts = true;
        satsolver_free(encoding_skolem->skolem);
        encoding_skolem->skolem = cs->skolem->skolem;
        
        skolem_propagate(encoding_skolem); // initial propagation
        for (unsigned i = 0; i < int_vector_count(c->decisions); i++) {
            Lit decision_lit = int_vector_get(c->decisions, i);
            if (skolem_is_deterministic(encoding_skolem, lit_to_var(decision_lit))) {
                V2("Discovered during replay that decision %d is not needed.\n", decision_lit);
            } else {
                skolem_decision(encoding_skolem, decision_lit);
            }
            skolem_propagate(encoding_skolem);
            assert(!skolem_is_conflicted(encoding_skolem));
        }
        
        V2("max satlit %d\n", satsolver_get_max_var(cs->skolem->skolem));
        skolem_encode_global_conflict_check(encoding_skolem); // this encodes the disjunction over the potentially conflicted variables.
        
#ifdef DEBUG // test if the function is correct
        for (unsigned i = 0; i < var_vector_count(c->qcnf->vars); i++) {
            abortif(qcnf_var_exists(c->qcnf, i) && ! skolem_is_deterministic(encoding_skolem, i), "A variable remained deterministic after casesplit replay.");
        }
        V1("Universal assumption is: ");
        for (unsigned i = 0; i < int_vector_count(c->universal_assumptions); i++) {
            Lit lit = int_vector_get(c->universal_assumptions, i);
            int satlit = skolem_get_satsolver_lit(cs->skolem, lit);
            satsolver_assume(cs->skolem->skolem, satlit);
            V1(" %d (%d)", lit, satlit);
        }
        V1("\n");
        
        sat_res res = satsolver_sat(cs->skolem->skolem);
        if (res != SATSOLVER_RESULT_UNSAT) {
            
            V1("Violating assignment is: ");
            for (unsigned i = 0; i < var_vector_count(c->qcnf->vars); i++) {
                if (qcnf_var_exists(c->qcnf, i) && qcnf_is_universal(c->qcnf, i)) {
                    int satlit = skolem_get_satsolver_lit(encoding_skolem, (Lit) i);
                    int orig_satlit = skolem_get_satsolver_lit(cs->skolem, (Lit) i);
                    int val = satsolver_deref(cs->skolem->skolem, orig_satlit);
                    V1(" %d (%d,%d)", val * (Lit) i, satlit, orig_satlit);
                }
            }
            V1("\n");
            abort();
        }
#endif
        
        encoding_skolem->skolem = NULL; // don't want to free the main sat solver
        skolem_free(encoding_skolem);
    }
}

void casesplits_completed_case_split(Casesplits* cs, int_vector* universal_assumptions, int_vector* decisions, QCNF* clauses) {
    Case* c = case_init();
    c->type = 1; // function case
    c->universal_assumptions = universal_assumptions;
    c->decisions = decisions;
    c->qcnf = clauses;
    vector_add(cs->solved_cases, c);
}

void casesplits_encode_case_into_satsolver(Skolem* s, Case* c, SATSolver* sat) {
    V2("Encoding completed case");
    NOT_IMPLEMENTED();
}

void casesplits_record_cegar_cube(Casesplits* cs, int_vector* cube, int_vector* partial_assignment) {
    Case* c = case_init();
    assert(cube);
    assert(!cs->options->certify_SAT || partial_assignment);
    c->type = 0;
    c->universal_assumptions = cube;
    c->decisions = partial_assignment;
    vector_add(cs->solved_cases, c);
    // TODO: Instead of adding a clause to the SATsolver only, we should add a clause to the actual QCNF to enable propagation among the universals. But universal reduction might collapse these clauses to empty clauses ... not good.
    V2("Completed cube (with length %u) ", int_vector_count(cube));
    for (unsigned i = 0; i < int_vector_count(cube); i++) {
        Lit lit = int_vector_get(cube, i);
        assert(skolem_is_deterministic(cs->skolem, lit_to_var(lit)));
        assert(skolem_get_decision_lvl(cs->skolem, lit_to_var(lit)) == 0);
        if (int_vector_count(cube) <= 10) {
            V2("%d ", lit);
        } else {
            V3("%d ", lit);
        }
        
        if (! map_contains(cs->original_satlits, - lit)) {
            // Stupid bug: after replenishing the sat solvers, the interface might shift and old cubes are not on the interface any more.
            abortif(cs->skolem->stack->push_count != 0, "This is a new bug");
            cegar_remember_original_satlit(cs, lit_to_var(lit));
        }
    }
    V2("\n");
}

void casesplits_record_case(Casesplits* cs) {
    casesplits_close_heuristics(cs, cs->skolem->universals_assumptions);
    
    int_vector* determinizations_with_polarity = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(cs->skolem->determinization_order); i++) {
        unsigned var_id = (unsigned) int_vector_get(cs->skolem->determinization_order, i);
        Lit lit = (Lit) var_id;
        int constant_val = skolem_get_constant_value(cs->skolem, (Lit) var_id);
        int decision_val = skolem_get_decision_val(cs->skolem, var_id);
        int pure_val = skolem_get_pure_val(cs->skolem, var_id);
        assert(! pure_val || ! decision_val);
        
        if (constant_val) {
            lit = constant_val * lit;
        } else if (decision_val) {
            lit = decision_val * lit;
        } else if (pure_val) {
            lit = pure_val * lit;
        }
        
        int_vector_add(determinizations_with_polarity, lit);
    }
    
    casesplits_completed_case_split(cs,
                                    int_vector_copy(cs->skolem->universals_assumptions),
                                    determinizations_with_polarity,
                                    qcnf_copy(cs->qcnf));
}

void casesplits_steal_cases(Casesplits* new_cs, Casesplits* old_cs) {
    for (unsigned i = 0; i < vector_count(old_cs->solved_cases); i++) {
        Case* c = (Case*) vector_get(old_cs->solved_cases, i);
        if (c->type == 0) {
            casesplits_record_cegar_cube(new_cs, c->universal_assumptions, c->decisions);
            // We passed these objects on to the new casesplits object, so make sure these
            // objects will not be deallocated during free of old_cs below.
            c->universal_assumptions = NULL;
            c->decisions = NULL;
            assert(c->qcnf == NULL);
        } else {
            assert(c->type == 1);
            // We passed these objects on to the new casesplits object, so make sure these
            // objects will not be deallocated during free of old_cs below.
            casesplits_completed_case_split(new_cs, c->universal_assumptions, c->decisions, c->qcnf);
            c->universal_assumptions = NULL;
            c->decisions = NULL;
            c->qcnf = NULL;
        }
    }
    casesplits_encode_last_case(new_cs);
}

void casesplits_print_statistics(Casesplits* d) {
    if (d && casesplits_is_initialized(d)) {
        V0("Domain statistics:\n");
        V0("  Interface size: %u\n", int_vector_count(d->interface_vars));
        V0("  Number of explored cases: %u\n", vector_count(d->solved_cases));
        V0("CEGAR statistics:\n");
        V0("  Successful minimizations: %u\n", d->cegar_stats.successful_minimizations);
        V0("  Additional assignments: %u\n", d->cegar_stats.additional_assignments_num);
        V0("  Additional assignments helped: %u\n", d->cegar_stats.successful_minimizations_by_additional_assignments);
    }
}
