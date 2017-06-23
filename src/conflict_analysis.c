//
//  conflict_analysis.c
//  cadet
//
//  Created by Markus Rabe on 25/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "conflict_analysis.h"
#include "log.h"

#include <assert.h>
#include <stdint.h>

typedef struct {
    C2* c2;
    worklist* queue; // literals
    int_vector* conflicting_assignment;
    void* domain;
    int (*domain_get_value)(void* domain, Lit lit);
    Clause* (*domain_get_reason)(void* domain, Lit lit);
    bool (*domain_is_legal_dependence)(void* domain, unsigned var_id, unsigned depending_on);
    unsigned (*domain_get_decision_lvl)(void* domain, unsigned var_id);
    
    unsigned conflicted_var_id;
    Clause* conflicted_clause;
    unsigned conflict_decision_lvl;
} conflict_analysis;

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
        assert(ca->domain_get_decision_lvl(ca->domain, lit_to_var(consequence)) >= ca->domain_get_decision_lvl(ca->domain, lit_to_var(l)) || ca->domain_get_value(ca->domain, consequence) == 1);
        
        if (! ca->domain_is_legal_dependence(ca->c2->skolem, lit_to_var(consequence), lit_to_var(l))) {
//            assert(ca->domain_get_value(ca->domain, l) == -1);
            int_vector_add(ca->conflicting_assignment, - l);
            continue;
        }
        
        assert(ca->c2->state != C2_SKOLEM_CONFLICT || skolem_get_unique_consequence((Skolem*) ca->domain, reason) == consequence || skolem_get_constant_value(ca->c2->skolem, consequence) == 1);
        
//        assert(ca->domain_get_value(ca->domain, l) == -1 || skolem_compare_dependencies(s, skolem_get_dependencies(s, lit_to_var(consequence)), skolem_get_dependencies(s, lit_to_var(l))) == DEPS_SMALLER );
//        assert(ca->domain_get_value(ca->domain, -l) == 1 || skolem_compare_dependencies(s, skolem_get_dependencies(s, lit_to_var(consequence)), skolem_get_dependencies(s, lit_to_var(l))) == DEPS_SMALLER);
        
        // activity heuristics
        if (!set_contains(ca->queue->s, (void*) (int64_t) - l)) {
            c2_increase_activity(ca->c2, (unsigned) abs(l), ca->c2->magic.implication_graph_variable_activity);
        }
        
        worklist_push(ca->queue, (void*) (int64_t) - l);
    }
}

//int skolem_get_value_for_conflict_analysis(void* domain, Lit lit) {
//    assert(lit != 0);
//    Skolem* s = (Skolem*) domain;
//    assert(skolem_is_deterministic(s, lit_to_var(lit)));
//    int satlit = skolem_get_satlit(s, lit);
//    return satsolver_deref(s->skolem, satlit);
//}

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

unsigned determine_cost(conflict_analysis* ca, Clause* c) {
    unsigned cost = 0;
    for (unsigned i = 0; i < c->size; i++) {
        if (! set_contains(ca->queue->s, (void*)(int64_t) - c->occs[i])) {
            cost++;
        }
    }
    return cost;
}

//Clause* conflict_analysis_find_reason_for_value(conflict_analysis* ca, Lit lit, bool* depends_on_illegals) {
//    assert(lit != 0);
//    Var* v = var_vector_get(ca->c2->qcnf->vars, lit_to_var(lit));
//    vector* occs = lit > 0 ? &v->pos_occs : &v->neg_occs;
//    
//    Clause* candidate = NULL;
//    unsigned candidate_cost = UINT_MAX;
//    bool depends_on_illegals_candidate = false;
//    for (unsigned i = 0; i < vector_count(occs); i++) {
//        Clause* c = vector_get(occs, i);
//        
//        // it is questionable whether this optimization actually helps as it requires us to keep another data structure in cache
//        if (!ca->domain_is_relevant_clause(ca->domain, c, lit)) {
//            continue;
//        }
//        if (is_reason_for_lit(ca, c, lit)) {
//            return c;
//        }
//    }
//    *depends_on_illegals = depends_on_illegals_candidate;
//    return candidate;
//}

bool legal_reason(conflict_analysis* ca, Lit lit, Clause* c) {
    for (int i = 0; i < c->size; i++) {
        if (c->occs[i] != lit && ! ca->domain_is_legal_dependence(ca->domain, lit_to_var(lit), lit_to_var(c->occs[i]))) {
            return false;
        }
    }
    return true;
}


void conflict_analysis_follow_implication_graph(conflict_analysis* ca) {
    
    while (worklist_count(ca->queue) > 0) {
        Lit lit = (Lit) worklist_pop(ca->queue);

        abortif(ca->c2->examples->state != EXAMPLES_STATE_INCONSISTENT_DECISION_CONFLICT && ca->c2->skolem->state != SKOLEM_STATE_BACKPROPAGATION_CONFLICT && ca->domain_get_value(ca->domain, lit) != 1, "Variable to track in conflict analysis has no value.");
        
        Var* v = var_vector_get(ca->c2->qcnf->vars, lit_to_var(lit));
        unsigned d_lvl = ca->domain_get_decision_lvl(ca->domain, lit_to_var(lit));
        assert(d_lvl <= ca->conflict_decision_lvl);
        
        bool is_value_decision = c2_is_decision_var(ca->c2, v->var_id) && skolem_get_constant_value(ca->c2->skolem, lit) == 1;
        
        if (v->is_universal || d_lvl < ca->conflict_decision_lvl || is_value_decision) {
            int_vector_add(ca->conflicting_assignment, lit);
        } else {
            Clause* reason = ca->domain_get_reason(ca->domain, lit); // conflict_analysis_find_reason_for_value(ca, lit, &depends_on_illegals);
            if (reason == NULL) {
                abortif(ca->c2->state == C2_SKOLEM_CONFLICT
                        && ca->c2->skolem->state != SKOLEM_STATE_BACKPROPAGATION_CONFLICT
                        && ! c2_is_decision_var(ca->c2, v->var_id), "No reason for lit %d found in conflict analysis.\n", lit);
//                assert(ca->c2->state == C2_EXAMPLES_CONFLICT && c2_is_decision_var(ca->c2, v->var_id)); // this means it was a decision variable for the example domain
                int_vector_add(ca->conflicting_assignment, lit); // must be decision variable (and conflict caused by this decision)
            } else if (!reason->consistent_with_originals) { // decision clause!
                assert(c2_is_decision_var(ca->c2, lit_to_var(lit)) || lit_to_var(lit) == ca->conflicted_var_id);
                int_vector_add(ca->conflicting_assignment, lit);
            } else if (!legal_reason(ca, lit, reason)) {
                int_vector_add(ca->conflicting_assignment, lit);
            } else {
                assert(reason->original || reason->consistent_with_originals);
                if (debug_verbosity >= VERBOSITY_HIGH) {
                    V3("  Reason for %d is clause %u: ", lit, reason->clause_id);
                    qcnf_print_clause(reason, stdout);
                }
                conflict_analysis_schedule_causing_vars_in_work_queue(ca, reason, lit);
            }
        }
    }
}

void ca_free(conflict_analysis* ca) {
    assert(worklist_count(ca->queue) == 0);
    worklist_free(ca->queue);
    free(ca);
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

// This probably corresponds to "local minimization", not "recursive minimization"
/* Minimizing Learned Clauses, Niklas Sorensson and Armin Biere */
/* Towards Understanding and Harnessing the Potential of Clause Learning, Paul Beame, Henry Kautz, and Ashish Sabharwal */
void conflict_analysis_minimize_conflicting_assignment(conflict_analysis* ca) {
    unsigned removed_num = 0;
    for (unsigned i = 0; i < int_vector_count(ca->conflicting_assignment); i++) {
        Lit lit = int_vector_get(ca->conflicting_assignment, i);
        Var* v = var_vector_get(ca->c2->qcnf->vars, (lit_to_var(lit)));
        vector* possible_implications = lit > 0 ? &v->pos_occs : &v->neg_occs;
        if (is_implied_by(ca, lit, possible_implications)) {
            int_vector_remove_index(ca->conflicting_assignment, i);
            removed_num += 1;
            i -= 1;
        }
    }
    ca->c2->statistics.successful_conflict_clause_minimizations += removed_num;
    V2("Conflict clause minimization removed %u literals.\n", removed_num);
}

unsigned dependency_size(C2 *c2, Var* v) {
    assert(! v->is_universal);
    Scope* scope = vector_get(c2->qcnf->scopes, v->scope_id);
    return int_vector_count(scope->vars);
}

int_vector* analyze_assignment_conflict(C2* c2,
                                        unsigned conflicted_var,
                                        Clause* conflicted_clause,
                                        void* domain,
                                        int  (*domain_get_value)(void* domain, Lit lit),
                                        Clause* (*domain_get_reason)(void* domain, Lit lit),
                                        bool (*domain_is_legal_dependence)(void* domain, unsigned var_id, unsigned depending_on),
                                        unsigned (*domain_get_decision_lvl)(void* domain, unsigned var_id)) {
    V3("Computing conflict clause. Conflicted var: %u. Conflicted clause: ", conflicted_var);
    if (conflicted_clause) {
        if (debug_verbosity >= VERBOSITY_HIGH) {
            qcnf_print_clause(conflicted_clause, stdout);
            V3(" with clause id %u\n", conflicted_clause->clause_id);
        }
    } else {
        V3("NULL\n");
    }
    
#ifdef DEBUG
    if (conflicted_var != 0) {
        Var* v_help = var_vector_get(c2->qcnf->vars, conflicted_var);
        assert(qcnf_is_existential(c2->qcnf, v_help->var_id));
    }
#endif
    
    conflict_analysis* ca = malloc(sizeof(conflict_analysis));
    ca->c2 = c2;
    ca->conflicting_assignment = int_vector_init();
    ca->queue = worklist_init_unique_computation(qcnf_compare_literals_by_var_id);
    ca->domain = domain;
    ca->conflicted_clause = conflicted_clause;
    ca->conflicted_var_id = conflicted_var;
    
    
    // Function pointers
    ca->domain_get_value = domain_get_value;
    ca->domain_get_reason = domain_get_reason;
    ca->domain_is_legal_dependence = domain_is_legal_dependence;
    ca->domain_get_decision_lvl = domain_get_decision_lvl;
    
    if (conflicted_clause) {
        // add literals of conflicted clause to worklist
        ca->conflict_decision_lvl = 0;
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
        ca->conflict_decision_lvl = domain_get_decision_lvl(domain, conflicted_var); // ca->c2->skolem->decision_lvl;
        
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
        Var* v_debug = var_vector_get(c2->qcnf->vars, lit_to_var(l_debug));
        abortif(!v_debug->original, "Conflict clause contains helper variables.\n");
        abortif(int_vector_contains(ca->conflicting_assignment, -l_debug), "Conflict clause contains positive and negative literal.\n");
    }
#endif
    
    if (c2->options->minimize_conflicts) {
        conflict_analysis_minimize_conflicting_assignment(ca);
    }
    
    int_vector* conflict = ca->conflicting_assignment;
    ca_free(ca);
    return conflict;
}
