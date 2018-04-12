//
//  casesplits.c
//  cadet
//
//  Created by Markus Rabe on 28/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#include "casesplits.h"
#include "log.h"
#include "c2_rl.h"

#include <math.h>

Casesplits* casesplits_init(QCNF* qcnf) {
    Casesplits* cs = malloc(sizeof(Casesplits));
    cs->skolem = NULL;
    cs->closed_cases = vector_init();
    
    cs->interface_vars = NULL;
    cs->interface_activities = float_vector_init();
    cs->original_satlits = map_init();
    
    // CEGAR
    cs->exists_solver = satsolver_init(); // no initialized yet; see domain_update_interface
    cs->additional_assignment = int_vector_init();
    cs->is_used_in_lemma = int_vector_init();
    
    // CEGAR statistics
    cs->cegar_stats.successful_minimizations = 0;
    cs->cegar_stats.additional_assignments_num = 0;
    cs->cegar_stats.successful_minimizations_by_additional_assignments = 0;
    cs->cegar_stats.recent_average_cube_size = 0;
    cs->cegar_magic.max_cegar_iterations_per_learnt_clause = 50;
    cs->cegar_magic.cegar_effectiveness_threshold = 17;
    cs->cegar_magic.universal_activity_decay = (float) 0.95;
    
    // Case statistics
    cs->case_generalizations = 0;
    
    return cs;
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
    
    // initialize vector of bits saying we need this variable in the blocking clause
    int_vector_reset(cs->is_used_in_lemma);
    for (unsigned i = 0; i < var_vector_count(cs->skolem->qcnf->vars); i++) {
        int_vector_add(cs->is_used_in_lemma, 1);
    }
    
    if (cs->exists_solver) {satsolver_free(cs->exists_solver);}
    cs->exists_solver = satsolver_init();
    
    const unsigned max_var_id = var_vector_count(cs->skolem->qcnf->vars);
    satsolver_set_max_var(cs->exists_solver, (int) max_var_id);
    
    // set up satsolver for existentials
    for (unsigned i = 0; i < vector_count(cs->skolem->qcnf->all_clauses); i++) {
        Clause* c = vector_get(cs->skolem->qcnf->all_clauses, i);
        if (! c->original) {
            continue;
        }
        Lit uc = skolem_get_unique_consequence(cs->skolem, c);
        if (uc != 0 && skolem_is_deterministic(cs->skolem, lit_to_var(uc))) {
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
    for (unsigned i = 0; i < vector_count(cs->skolem->qcnf->all_clauses); i++) {
        Clause* c = vector_get(cs->skolem->qcnf->all_clauses, i);
        if (! c->original || c->blocked) {
            continue;
        }
        Lit uc = skolem_get_unique_consequence(cs->skolem, c);
        if (uc != 0 && skolem_is_deterministic(cs->skolem, lit_to_var(uc))) {
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
    
    V1("Total of %u deterministic vars\n", int_vector_count(cs->skolem->determinization_order));
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
    if (c->determinization_order) {int_vector_free(c->determinization_order);}
    if (c->unique_consequences) {int_vector_free(c->unique_consequences);}
    if (c->potentially_conflicted_variables) {int_vector_free(c->potentially_conflicted_variables);}
    free(c);
}

void casesplits_free(Casesplits* d) {
    if (d->exists_solver) {satsolver_free(d->exists_solver);}
    if (d->interface_vars) {int_vector_free(d->interface_vars);}
    if (d->interface_activities) {float_vector_free(d->interface_activities);}
    if (d->original_satlits) {map_free(d->original_satlits);}
    int_vector_free(d->is_used_in_lemma);
    for (unsigned i = 0; i < vector_count(d->closed_cases); i++) {
        case_free((Case*) vector_get(d->closed_cases, i));
    }
    vector_free(d->closed_cases);
}


Case* case_init() {
    Case* c = malloc(sizeof(Case));
    c->type = 0;
    c->universal_assumptions = NULL;
    c->determinization_order = NULL;
    c->unique_consequences = NULL;
    c->potentially_conflicted_variables = NULL;
    return c;
}

void casesplits_close_heuristics(Casesplits* cs, int_vector* solved_cube) {
    if (int_vector_count(solved_cube) < 20) { // prevent tinitiny increments, NaN-hell, etc
        float activity_bump = (float) ((double) 1.0 / pow(2.0, (double) int_vector_count(solved_cube)));
        //        float activity_bump = (float) ((double) 1.0 / (double) (c2->case_split_depth * c2->case_split_depth + 1.0));
        V3("Activity bump: %f\n", activity_bump);
        for (unsigned i = 0; i < int_vector_count(solved_cube); i++) {
            unsigned var_id = lit_to_var(int_vector_get(solved_cube, i));
            casesplits_add_interface_activity(cs, var_id, activity_bump);
        }
    }
}

void skolem_is_assignment_possible(Skolem* s, int_vector* ass) {
    for (unsigned i = 0; i < int_vector_count(ass); i++) {
        Lit lit = int_vector_get(ass, i);
        int satlit = skolem_get_satsolver_lit(s, lit);
        satsolver_assume(s->skolem, satlit);
    }
    sat_res res = satsolver_sat(s->skolem);
    if (res == SATSOLVER_UNSAT) {
        V1("Illegally excluded assignment.\n");
        abort();
    }
}

void skolem_print_assignment(Skolem* s) {
    V1("Assignment is:")
    for (unsigned i = 0; i < var_vector_count(s->qcnf->vars); i++) {
        if (qcnf_var_exists(s->qcnf, i)) {
            assert(skolem_is_deterministic(s, i));
            int satlit_pos = skolem_get_satsolver_lit(s,   (Lit) i);
            int satlit_neg = skolem_get_satsolver_lit(s, - (Lit) i);
            int satval_pos = satsolver_deref(s->skolem, satlit_pos);
            int satval_neg = satsolver_deref(s->skolem, satlit_neg);
            if (satval_pos != - satval_neg) {
                LOG_WARNING(" Variable %u is conflicted! ", i);
            }
            V1(" %d", satval_pos * (Lit) i);
        }
    }
    V1("\n");
}

void casesplits_record_conflicts(Skolem* s, int_vector* decision_sequence) {
    s->record_conflicts = true;
    skolem_propagate(s); // initial propagation
    for (unsigned i = 0; i < int_vector_count(decision_sequence); i++) {
        Lit decision_lit = int_vector_get(decision_sequence, i);
        if (skolem_is_deterministic(s, lit_to_var(decision_lit))) {
            V3("Discovered during replay that decision %d is not needed.\n", decision_lit);
        } else {
            skolem_decision(s, decision_lit);
            skolem_propagate(s);
            assert(!skolem_is_conflicted(s)); // as we are in conflict recording mode
        }
    }
    V2("max satlit %d\n", satsolver_get_max_var(s->skolem));
    s->record_conflicts = false;
}

int_vector* casesplits_test_assumptions(Casesplits* cs, int_vector* universal_assumptions) {
    V1("Testing assumption of closed case\n");
    for (unsigned i = 0; i < int_vector_count(universal_assumptions); i++) {
        Lit lit = int_vector_get(universal_assumptions, i);
        assert(skolem_is_deterministic(cs->skolem, lit_to_var(lit)));
        int satlit = (int) (long) map_get(cs->original_satlits, lit);
        assert(satlit != - cs->skolem->satlit_true);
        satsolver_assume(cs->skolem->skolem, satlit);
    }
    
    sat_res res = satsolver_sat(cs->skolem->skolem);
    if (res == SATSOLVER_UNSAT) {
        int_vector* failed_as = int_vector_init();
        for (unsigned i = 0; i < int_vector_count(universal_assumptions); i++) {
            Lit lit = int_vector_get(universal_assumptions, i);
            int satlit = (int) (long) map_get(cs->original_satlits, lit);
            if (satsolver_failed_assumption(cs->skolem->skolem, satlit)) {
                int_vector_add(failed_as, lit);
            }
        }
        return failed_as;
    } else {
        return NULL;
    }
}


Case* casesplits_completed_case_split(Casesplits* cs,
                                      int_vector* universal_assumptions,
                                      int_vector* determinization_order,
                                      int_vector* unique_consequences,
                                      int_vector* potentially_conflicted_variables) {
    
    Case* c = case_init();
    c->type = 1; // function case
    c->universal_assumptions = universal_assumptions;
    c->determinization_order = determinization_order;
    c->unique_consequences = unique_consequences;
    c->potentially_conflicted_variables = potentially_conflicted_variables;
    vector_add(cs->closed_cases, c);
    return c;
}


void casesplits_encode_closed_case(Casesplits* cs, int_vector* determinization_order, int_vector* universal_assumptions) {
    assert(cs->skolem->decision_lvl == 0);
    assert(!skolem_is_conflicted(cs->skolem));
    assert(!cs->skolem->record_conflicts);
    
    rl_mute();
    stack_push(cs->skolem->stack);
    
    // Encode the disjunction over the potentially conflicted variables.
    // This excludes all solutions for which this Skolem function works
    casesplits_record_conflicts(cs->skolem, determinization_order);
    int_vector_free(determinization_order);
    determinization_order = case_splits_determinization_order_with_polarities(cs->skolem);
    int_vector* potentially_conflicted_variables = int_vector_copy(cs->skolem->potentially_conflicted_variables);
    int_vector* unique_consequences = int_vector_copy(cs->skolem->unique_consequence);
    //#ifdef DEBUG
    //        for (unsigned i = 0; i < int_vector_count(c->determinization_order); i++) {
    //            int d = int_vector_get(c->determinization_order, i);
    //            int d2 = int_vector_get(cs->skolem->determinization_order, i);
    //            assert(d == d2);
    //        }
    //        for (unsigned i = 0; i < int_vector_count(c->unique_consequences); i++) {
    //            Clause* cl = vector_get(cs->skolem->qcnf->all_clauses, i);
    //            assert(cl);
    //            unsigned uc = lit_to_var(int_vector_get(c->unique_consequences, i));
    //            if (uc == 0) {
    //                continue;
    //            }
    //            for (unsigned j = 0; j < cl->size; j++) {
    //                unsigned occ = lit_to_var(cl->occs[j]);
    //                assert(   skolem_get_decision_lvl(cs->skolem, occ)
    //                       <= skolem_get_decision_lvl(cs->skolem, uc));
    //            }
    //        }
    //#endif
    
    if ( ! cs->skolem->options->functional_synthesis) {
        skolem_encode_global_conflict_check(cs->skolem);
        int_vector* necessary_assumptions = casesplits_test_assumptions(cs, universal_assumptions);
        abortif(necessary_assumptions == NULL, "Case split was not successfully closed");
        for (unsigned i = 0; i < int_vector_count(necessary_assumptions); i++) {
            Lit lit = int_vector_get(necessary_assumptions, i);
            int satlit = (int) (long) map_get(cs->original_satlits, - lit);
            satsolver_add(cs->skolem->skolem, satlit);
        }
        satsolver_clause_finished(cs->skolem->skolem);
        unsigned generalizations = int_vector_count(universal_assumptions) - int_vector_count(necessary_assumptions);
        cs->case_generalizations += generalizations;
        if (generalizations > 0) {
            V1("Generalized assumptions! Removed %d of %d assignments\n",
               generalizations,
               int_vector_count(universal_assumptions));
        }
        
        int_vector_free(universal_assumptions);
        universal_assumptions = necessary_assumptions;
        casesplits_close_heuristics(cs, universal_assumptions);
    } else { // functional synthesis!
        abortif(int_vector_count(universal_assumptions) != 0,
                "Case splits and functional synthesis are not supported together atm.");
        satsolver_clause_finished(cs->skolem->skolem); // make the formula UNSAT no matter what
        skolem_encode_global_conflict_check(cs->skolem);
    }
    
#ifdef DEBUG
    for (unsigned i = 0; i < var_vector_count(cs->skolem->qcnf->vars); i++) {
        abortif(qcnf_var_exists(cs->skolem->qcnf, i) && ! skolem_is_deterministic(cs->skolem, i), "A variable remained deterministic after casesplit replay.");
    }
#endif
    
    stack_pop(cs->skolem->stack, cs->skolem);
    rl_unmute();
    
    casesplits_completed_case_split(cs,
                                    universal_assumptions,
                                    determinization_order,
                                    unique_consequences,
                                    potentially_conflicted_variables);
}


void casesplits_encode_CEGAR_case(Casesplits* cs) {
    
    Case* c = vector_get(cs->closed_cases, vector_count(cs->closed_cases) - 1);
    if (c->type == 0 || (c->type == 1 && cs->skolem->options->casesplits_cubes)) { // cube case
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
        abort(); // call casesplits_close
    }
}


void casesplits_encode_case_into_satsolver(Skolem* s, Case* c, SATSolver* sat) {
    V2("Encoding completed case");
    NOT_IMPLEMENTED();
}

void casesplits_record_cegar_cube(Casesplits* cs, int_vector* cube, int_vector* partial_assignment) {
    Case* c = case_init();
    assert(cube);
    assert(!cs->skolem->options->certify_SAT || partial_assignment);
    c->type = 0;
    c->universal_assumptions = cube;
    c->determinization_order = partial_assignment;
    vector_add(cs->closed_cases, c);
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

int case_splits_variable_polarity(Skolem* s, unsigned var_id) {
    int constant_val = skolem_get_constant_value(s, (Lit) var_id);
    int decision_val = skolem_get_decision_val(s, var_id);
    int pure_val = skolem_get_pure_val(s, var_id);
    assert(! pure_val || ! decision_val); // cannot be pure and decision at the same time
    int polarity = 1;
    if (constant_val) {
        polarity = constant_val;
    } else if (decision_val) {
        polarity = decision_val;
    } else if (pure_val) {
        polarity = - pure_val;
    }
    assert(polarity == -1 || polarity == 1);
    return polarity;
}

int_vector* case_splits_determinization_order_with_polarities(Skolem* s) {
    int_vector* result = int_vector_init();
    for (unsigned i = 0; i < int_vector_count(s->determinization_order); i++) {
        unsigned var_id = (unsigned) int_vector_get(s->determinization_order, i);
        int_vector_add(result, case_splits_variable_polarity(s, var_id) * (Lit) var_id);
    }
    return result;
}

void casesplits_steal_cases(Casesplits* new_cs, Casesplits* old_cs) {
    LOG_WARNING("This function is deprecated.");
    for (unsigned i = 0; i < vector_count(old_cs->closed_cases); i++) {
        Case* c = (Case*) vector_get(old_cs->closed_cases, i);
        if (c->type == 0) {
            casesplits_record_cegar_cube(new_cs, c->universal_assumptions, c->determinization_order);
            // We passed these objects on to the new casesplits object, so make sure these
            // objects will not be deallocated during free of old_cs below.
            c->universal_assumptions = NULL;
            c->determinization_order = NULL;
            assert(c->unique_consequences == NULL);
            casesplits_encode_CEGAR_case(new_cs);
        } else {
            assert(c->type == 1);
            // We passed these objects on to the new casesplits object, so make sure these
            // objects will not be deallocated during free of old_cs below.
            casesplits_encode_closed_case(new_cs, c->determinization_order, c->universal_assumptions);
            c->universal_assumptions = NULL;
            c->determinization_order = NULL;
            c->unique_consequences = NULL;
        }
    }
}

void casesplits_print_statistics(Casesplits* cs) {
    if (cs && casesplits_is_initialized(cs)) {
        V0("Domain statistics:\n");
        V0("  Interface size: %u\n", int_vector_count(cs->interface_vars));
        unsigned cegar_cases = 0;
        unsigned case_splits = 0;
        for (unsigned i = 0; i < vector_count(cs->closed_cases); i++) {
            Case* c = vector_get(cs->closed_cases, i);
            if (c->type == 0) {
                cegar_cases += 1;
            } else {
                case_splits += 1;
            }
        }
        V0("  Number of case splits: %u\n", case_splits);
        V0("  Successful minimizations: %u\n", cs->case_generalizations);
        V0("CEGAR statistics:\n");
        V0("  Number of cegar cases: %u\n", cegar_cases);
        V0("  Successful minimizations: %u\n", cs->cegar_stats.successful_minimizations);
        V0("  Additional assignments: %u\n", cs->cegar_stats.additional_assignments_num);
        V0("  Additional assignments helped: %u\n", cs->cegar_stats.successful_minimizations_by_additional_assignments);
    }
}
