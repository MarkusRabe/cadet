//
//  conflict_analysis.c
//  cadet
//
//  Created by Markus Rabe on 25/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "conflict_analysis.h"
#include "log.h"
#include "c2_rl.h"

#include <assert.h>
#include <stdint.h>


bool conflict_analysis_is_fresh(conflict_analysis* ca) {
    assert(int_vector_count(ca->conflicting_assignment) == 0);
    assert(int_vector_count(ca->resolutions_of_last_conflict) == 0);
    assert(worklist_count(ca->queue) == 0);
    assert(ca->domain == NULL);
    assert(ca->conflicted_clause == NULL);
    assert(ca->conflicted_var_id == 0);
    assert(ca->domain_get_value == NULL);
    assert(ca->domain_is_relevant_clause == NULL);
    assert(ca->domain_is_legal_dependence == NULL);
    assert(ca->domain_get_decision_lvl == NULL);
    return true;
}

void conflict_analsysis_reset(conflict_analysis* ca) {
    int_vector_reset(ca->conflicting_assignment);
    int_vector_reset(ca->resolutions_of_last_conflict);
    worklist_reset(ca->queue);
    ca->domain = NULL;
    ca->conflicted_clause = NULL;
    ca->conflicted_var_id = 0;
    ca->domain_get_value = NULL;
    ca->domain_is_relevant_clause = NULL;
    ca->domain_is_legal_dependence = NULL;
    ca->domain_get_decision_lvl = NULL;
    ca->conflict_decision_lvl = 0;
    
    assert(conflict_analysis_is_fresh(ca));
}

conflict_analysis* conflcit_analysis_init(C2* c2) {
    
    conflict_analysis* ca = malloc(sizeof(conflict_analysis));
    ca->c2 = c2;
    ca->conflicting_assignment = int_vector_init();
    ca->queue = worklist_init_unique_computation(qcnf_compare_literals_by_var_id);
    ca->resolution_graph = map_init();
    ca->resolutions_of_last_conflict = int_vector_init();
    
    conflict_analsysis_reset(ca);
    
    assert(conflict_analysis_is_fresh(ca));
    return ca;
}

void conflict_analysis_free(conflict_analysis* ca) {
    int_vector_free(ca->conflicting_assignment);
    worklist_free(ca->queue);
    int_vector_free(ca->resolutions_of_last_conflict);
    for (unsigned i = 0; i < vector_count(ca->c2->qcnf->all_clauses); i++) {
        if (map_contains(ca->resolution_graph, (int) i)) {
            int_vector* resolutions = map_get(ca->resolution_graph, (int) i);
            int_vector_free(resolutions);
        }
    }
    map_free(ca->resolution_graph);
    free(ca);
}

unsigned conflict_analysis_get_decision_lvl(conflict_analysis*  ca, unsigned var_id) {
    if (ca->conflicted_var_id == var_id) {
        return ca->c2->skolem->decision_lvl;
    } else {
        return ca->domain_get_decision_lvl(ca->domain, var_id);
    }
}

void conflict_analysis_schedule_causing_vars_in_work_queue(conflict_analysis* ca, Clause* reason, Lit consequence) {
    assert(consequence != 0);
    assert(lit_to_var(consequence) < var_vector_count(ca->c2->qcnf->vars));
    assert(ca->c2->skolem->conflict_var_id == lit_to_var(consequence)
           || ca->domain_get_value(ca->domain, consequence) == 1);
    assert(ca->domain != ca->c2->skolem || skolem_get_unique_consequence(ca->c2->skolem, reason) == consequence || skolem_get_constant_value(ca->c2->skolem, consequence) == 1); // a bit hacky
    
    for (unsigned i = 0; i < reason->size; i++) {
        Lit l = reason->occs[i];
        if (consequence == l) { // not strictly necessary
            continue;
        }
        assert(conflict_analysis_get_decision_lvl(ca, lit_to_var(consequence)) >= ca->domain_get_decision_lvl(ca->domain, lit_to_var(l)) || ca->domain_get_value(ca->domain, consequence) == 1);
        
        if (! ca->domain_is_legal_dependence(ca->c2->skolem, lit_to_var(consequence), lit_to_var(l))) {
            assert(ca->domain_get_value(ca->domain, l) == -1);
            int_vector_add(ca->conflicting_assignment, - l);
            continue;
        }
        
        assert(ca->c2->state != C2_SKOLEM_CONFLICT || skolem_get_unique_consequence((Skolem*) ca->domain, reason) == consequence || skolem_get_constant_value(ca->c2->skolem, consequence) == 1);
        
        assert(ca->domain_get_value(ca->domain, l) == -1);
        assert(ca->domain_get_value(ca->domain, -l) == 1);
        
        // activity heuristics
        if (!set_contains(ca->queue->s, (void*) (int64_t) - l)) {
            c2_increase_activity(ca->c2, (unsigned) abs(l), ca->c2->magic.activity_bump_value);
        }
        
        worklist_push(ca->queue, (void*) (int64_t) - l);
    }
}

bool conflict_analysis_depends_only_on_legals(conflict_analysis* ca, Clause* c, Lit lit) {
    assert(qcnf_contains_literal(c, lit));
    for (unsigned i = 0; i < c->size; i++) {
        Lit other = c->occs[i];
        assert(other != - lit); // no tautological clauses
        if (other == lit) {continue;}
        if (!ca->domain_is_legal_dependence(ca->c2->skolem, lit_to_var(lit), lit_to_var(other))) {
            return false;
        }
    }
    return true;
}

bool is_reason_for_lit(conflict_analysis* ca, Clause* c, Lit lit) {
    assert(ca->c2->skolem->conflict_var_id == lit_to_var(lit) || ca->domain_get_value(ca->domain, lit) == 1);
    assert(qcnf_contains_literal(c, lit));
    for (unsigned i = 0; i < c->size; i++) {
        Lit other = c->occs[i];
        assert(other != - lit);
        if (other == lit) {continue;}
        if (ca->domain_get_value(ca->domain, - other) != 1) { // all others must be surely false, if one of them isn't then the clause cannot be used as reason. This allows us to use conflicted variables as reasons.
            return false;
        }
    }
    return true;
}

unsigned determine_cost(conflict_analysis* ca, Clause* c) {
    unsigned cost = 0;
    for (unsigned i = 0; i < c->size; i++) {
        if (! set_contains(ca->queue->s, (void*)(int64_t) - c->occs[i])) {
            cost++;
        }
    }
    return cost;
}

Clause* conflict_analysis_find_reason_for_value(conflict_analysis* ca, Lit lit, bool* depends_on_illegals) {
    assert(lit != 0);
    Var* v = var_vector_get(ca->c2->qcnf->vars, lit_to_var(lit));
    vector* occs = lit > 0 ? &v->pos_occs : &v->neg_occs;
    
    Clause* candidate = NULL;
    unsigned candidate_cost = UINT_MAX;
    bool depends_on_illegals_candidate = false;
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = vector_get(occs, i);
        
        // it is questionable whether this optimization actually helps as it requires us to keep another data structure in cache
        if (!ca->domain_is_relevant_clause(ca->domain, c, lit)) {
            continue;
        }
        if (is_reason_for_lit(ca, c, lit)) {
            unsigned cost = determine_cost(ca, c);
            if (candidate == NULL || !candidate->consistent_with_originals || (cost < candidate_cost && c->consistent_with_originals)) { // TODO: prefer clauses that have only legal dependencies 
                candidate = c;
                candidate_cost = cost;
                depends_on_illegals_candidate = ! conflict_analysis_depends_only_on_legals(ca, c, lit);
            }
            if (cost == 0) {
                break; // unlikely
            }
        }
    }
    *depends_on_illegals = depends_on_illegals_candidate;
    return candidate;
}

void conflict_analysis_follow_implication_graph(conflict_analysis* ca) {
    
    while (worklist_count(ca->queue) > 0) {
        Lit lit = (Lit) worklist_pop(ca->queue);
        unsigned var_id = lit_to_var(lit);
        abortif(ca->c2->examples->state != EXAMPLES_STATE_INCONSISTENT_DECISION_CONFLICT && ca->domain_get_value(ca->domain, lit) != 1, "Variable to track in conflict analysis has no value.");
        unsigned d_lvl = conflict_analysis_get_decision_lvl(ca, var_id);
        assert(d_lvl <= ca->conflict_decision_lvl);
        
        if (d_lvl < ca->conflict_decision_lvl) {
            int_vector_add(ca->conflicting_assignment, lit);
        } else {
            bool depends_on_illegals = false;
            Clause* reason = conflict_analysis_find_reason_for_value(ca, lit, &depends_on_illegals);
            if (reason) {
                if (reason->consistent_with_originals || reason->is_cube) { // universal constraints clause (cube) or decision clause
                    if (debug_verbosity >= VERBOSITY_HIGH) {
                        V3("  Reason for %d is clause %u: ", lit, reason->clause_idx);
                        qcnf_print_clause(reason, stdout);
                    }
                    int_vector_add(ca->resolutions_of_last_conflict, (int) reason->clause_idx);
                    conflict_analysis_schedule_causing_vars_in_work_queue(ca, reason, lit);
                } else {
                    assert(skolem_is_decision_var(ca->c2->skolem, lit_to_var(lit)) || lit_to_var(lit) == ca->conflicted_var_id);
                    int_vector_add(ca->conflicting_assignment, lit);
                }
            } else {
                abortif(ca->c2->state == C2_SKOLEM_CONFLICT
                        && ! skolem_is_decision_var(ca->c2->skolem, var_id)
                        && ! int_vector_contains(ca->c2->skolem->universals_assumptions, lit)
                        && ! qcnf_is_universal(ca->c2->qcnf, var_id),
                        "No reason for lit %d found in conflict analysis.\n", lit);
                int_vector_add(ca->conflicting_assignment, lit);
                // TODO: this is where assumptions for incremental solving would come in
            }
        }
    }
}

bool is_implied_by(conflict_analysis* ca, Lit lit, vector* possible_implications) {
    for (unsigned i = 0; i < vector_count(possible_implications); i++) {
        Clause* c = vector_get(possible_implications, i);
        if (c->size < int_vector_count(ca->conflicting_assignment)) { // otherwise impossible to imply something
            bool all_but_lit_contained_negated = true;
            for (unsigned j = 0; j < c->size; j++) {
                if (c->occs[j] != lit && ! int_vector_contains(ca->conflicting_assignment, - c->occs[j])) {
                    all_but_lit_contained_negated = false;
                    break;
                }
            }
            if (all_but_lit_contained_negated) {
                V4("Found a implication to minimize conflict clause: ");
                if (debug_verbosity >= VERBOSITY_ALL) {
                    qcnf_print_clause(c, stdout);
                }
                return true;
            }
        }
    }
    return false;
}

unsigned dependency_size(C2 *c2, Var* v) {
    assert(! v->is_universal);
    Scope* scope = vector_get(c2->qcnf->scopes, v->scope_id);
    return int_vector_count(scope->vars);
}

Clause* analyze_conflict(conflict_analysis* ca,
                                        unsigned conflicted_var,
                                        Clause* conflicted_clause,
                                        void* domain,
                                        int  (*domain_get_value)(void* domain, Lit lit),
                                        bool (*domain_is_relevant_clause)(void* domain, Clause* c, Lit lit),
                                        bool (*domain_is_legal_dependence)(void* domain, unsigned var_id, unsigned depending_on),
                                        unsigned (*domain_get_decision_lvl)(void* domain, unsigned var_id)) {
    V3("Computing conflict clause. Conflicted var: %u. Conflicted clause:", conflicted_var);
    if (conflicted_clause) {
        V3("%u\n", conflicted_clause->clause_idx);
    } else {
        V3("NULL\n");
    }
    
    conflict_analsysis_reset(ca);
    
    assert(conflict_analysis_is_fresh(ca));
    
    ca->domain = domain;
    ca->conflicted_clause = conflicted_clause;
    ca->conflicted_var_id = conflicted_var;
    
    // Function pointers
    ca->domain_get_value = domain_get_value;
    ca->domain_is_relevant_clause = domain_is_relevant_clause;
    ca->domain_is_legal_dependence = domain_is_legal_dependence;
    ca->domain_get_decision_lvl = domain_get_decision_lvl;
    
    if (conflicted_clause) {
        // add literals of conflicted clause to worklist
        ca->conflict_decision_lvl = 0;
        int_vector_add(ca->resolutions_of_last_conflict, (int) conflicted_clause->clause_idx);
        for (unsigned i = 0; i < conflicted_clause->size; i++) {
            Lit l = conflicted_clause->occs[i];
            unsigned var_id = lit_to_var(l);
            assert(var_id == conflicted_var || ca->domain_get_value(ca->domain, l) == -1);
            worklist_push(ca->queue, (void*) (int64_t) - l);
            if (domain_get_decision_lvl(domain, var_id) > ca->conflict_decision_lvl) {
                ca->conflict_decision_lvl = domain_get_decision_lvl(domain, var_id);
            }
        }
    } else {
        assert(conflicted_var != 0);
        ca->conflict_decision_lvl = ca->c2->skolem->decision_lvl;
        
        assert(domain_get_value(domain,   (Lit) conflicted_var) == 1);
        assert(domain_get_value(domain, - (Lit) conflicted_var) == 1);
        worklist_push(ca->queue, (void*) (int64_t) conflicted_var);
        worklist_push(ca->queue, (void*) - (int64_t) conflicted_var);
    }
    
    conflict_analysis_follow_implication_graph(ca);
    
    V2("Conflict: ");
    if (debug_verbosity >= VERBOSITY_MEDIUM) {
        int_vector_print(ca->conflicting_assignment);
    }
    
#ifdef DEBUG
    for (unsigned i = 0; i < int_vector_count(ca->conflicting_assignment); i++) {
        Lit l_debug = int_vector_get(ca->conflicting_assignment, i);
        Var* v_debug = var_vector_get(ca->c2->qcnf->vars, lit_to_var(l_debug));
        abortif(!v_debug->original, "Conflict clause contains helper variables.\n");
        abortif(int_vector_contains(ca->conflicting_assignment, -l_debug), "Conflict clause contains positive and negative literal.\n");
    }
#endif
    
    // Create learnt clause and remember which other clauses it was resolved from
    for (unsigned i = 0; i < int_vector_count(ca->conflicting_assignment); i++) {
        qcnf_add_lit(ca->c2->qcnf, - int_vector_get(ca->conflicting_assignment, i));
    }
    Clause* c = qcnf_close_clause(ca->c2->qcnf);
    abortif(!c, "Learnt clause could not be created");
    c->original = 0;
    map_add(ca->resolution_graph, (int) c->clause_idx, ca->resolutions_of_last_conflict);
    ca->resolutions_of_last_conflict = int_vector_init();
    c2_rl_new_clause(c);
    return c;
}
