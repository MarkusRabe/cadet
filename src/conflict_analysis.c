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
    worklist* queue[2]; // a pair of queues for the two values of the conflicted variable; contains literals
    
    int_vector* conflicting_assignments[2]; // a pair int_vector*. Represents clauses derived for conflicted variable being true and false
//    int_vector* conflicting_assignment;
    
    void* domain;
    int (*domain_get_value)(void* domain, Lit lit, bool second_copy);
    Clause* (*domain_get_reason)(void* domain, Lit lit, bool second_copy);
    bool (*domain_is_legal_dependence)(void* domain, unsigned var_id, unsigned depending_on);
    unsigned (*domain_get_decision_lvl)(void* domain, unsigned var_id);
    
    unsigned conflicted_var_id;
    Clause* conflicted_clause;
    unsigned conflict_decision_lvl;
} conflict_analysis;

void conflict_analysis_schedule_causing_vars_in_work_queue(conflict_analysis* ca, Clause* reason, Lit consequence, int copy) {
    assert(consequence != 0);
    assert(lit_to_var(consequence) < var_vector_count(ca->c2->qcnf->vars));
    assert(ca->c2->skolem->conflict_var_id == lit_to_var(consequence)
           || ca->domain_get_value(ca->domain, consequence, copy) == 1);
    assert(ca->domain != ca->c2->skolem || skolem_get_unique_consequence(ca->c2->skolem, reason) == consequence || skolem_get_constant_value(ca->c2->skolem, consequence) == 1); // a bit hacky
    
    for (unsigned i = 0; i < reason->size; i++) {
        Lit l = reason->occs[i];
        if (consequence == l) { // not strictly necessary
            continue;
        }
        assert(ca->domain_get_decision_lvl(ca->domain, lit_to_var(consequence)) >= ca->domain_get_decision_lvl(ca->domain, lit_to_var(l)) || ca->domain_get_value(ca->domain, consequence, 0) == 1);
        
        if (! ca->domain_is_legal_dependence(ca->c2->skolem, lit_to_var(consequence), lit_to_var(l))) {
//            assert(ca->domain_get_value(ca->domain, l) == -1);
            int_vector_add(ca->conflicting_assignments[copy], - l);
            continue;
        }
        
        assert(ca->c2->state != C2_SKOLEM_CONFLICT || skolem_get_unique_consequence((Skolem*) ca->domain, reason) == consequence || skolem_get_constant_value(ca->c2->skolem, consequence) == 1);
        
        // activity heuristics
        if (!set_contains(ca->queue[copy]->s, (void*) (int64_t) - l)) {
            c2_increase_activity(ca->c2, (unsigned) abs(l), ca->c2->magic.implication_graph_variable_activity);
        }
        
        worklist_push(ca->queue[copy], (void*) (int64_t) - l);
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

bool legal_reason(conflict_analysis* ca, Lit lit, Clause* c, int copy) {
    assert(copy == 0 || copy == 1);
    for (int i = 0; i < c->size; i++) {
        if (c->occs[i] != lit && ca->domain_get_value(ca->domain, c->occs[i], copy) != -1) {
//        if (c->occs[i] != lit && ! ca->domain_is_legal_dependence(ca->domain, lit_to_var(lit), lit_to_var(c->occs[i]))) {
            return false;
        }
    }
    return true;
}


bool is_implied_by(conflict_analysis* ca, Lit lit, vector* possible_implications, int_vector* conflicting_assignment) {
    for (unsigned i = 0; i < vector_count(possible_implications); i++) {
        Clause* c = vector_get(possible_implications, i);
        if (c->size < int_vector_count(conflicting_assignment)) { // otherwise impossible to imply something
            bool all_but_lit_contained_negated = true;
            for (unsigned j = 0; j < c->size; j++) {
                if (c->occs[j] != lit && ! int_vector_contains(conflicting_assignment, - c->occs[j])) {
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
void conflict_analysis_minimize_conflicting_assignment(conflict_analysis* ca, int_vector* conflicting_assignment) {
    unsigned removed_num = 0;
    for (unsigned i = 0; i < int_vector_count(conflicting_assignment); i++) {
        Lit lit = int_vector_get(conflicting_assignment, i);
        Var* v = var_vector_get(ca->c2->qcnf->vars, (lit_to_var(lit)));
        vector* possible_implications = lit > 0 ? &v->pos_occs : &v->neg_occs;
        if (is_implied_by(ca, lit, possible_implications, conflicting_assignment)) {
            int_vector_remove_index(conflicting_assignment, i);
            removed_num += 1;
            i -= 1;
        }
    }
    ca->c2->statistics.successful_conflict_clause_minimizations += removed_num;
    V2("Conflict clause minimization removed %u literals.\n", removed_num);
}


void conflict_analysis_follow_implication_graph(conflict_analysis* ca, int copy) {
    assert(copy == 0 || copy == 1);
    
    while (worklist_count(ca->queue[copy]) > 0) {
        Lit lit = (Lit) worklist_pop(ca->queue[copy]);

        abortif(ca->c2->examples->state != EXAMPLES_STATE_INCONSISTENT_DECISION_CONFLICT && ca->c2->skolem->state != SKOLEM_STATE_BACKPROPAGATION_CONFLICT && ca->domain_get_value(ca->domain, lit, copy) != 1, "Variable to track in conflict analysis has no value (in the right copy).");
        
        Var* v = var_vector_get(ca->c2->qcnf->vars, lit_to_var(lit));
        unsigned d_lvl = ca->domain_get_decision_lvl(ca->domain, lit_to_var(lit));
        assert(d_lvl <= ca->conflict_decision_lvl);
        
//        bool is_value_decision = c2_is_decision_var(ca->c2, v->var_id) && skolem_get_constant_value(ca->c2->skolem, lit) == 1; // TODO: remove the value decision case; treat it as normal decisions
        
        if (v->is_universal || d_lvl < ca->conflict_decision_lvl) {
            int_vector_add(ca->conflicting_assignments[copy], lit);
        } else {
            Clause* reason = ca->domain_get_reason(ca->domain, lit, copy); // conflict_analysis_find_reason_for_value(ca, lit, &depends_on_illegals);
            if (reason == NULL) {
                abortif(ca->c2->state == C2_SKOLEM_CONFLICT
                        && ca->c2->skolem->state != SKOLEM_STATE_BACKPROPAGATION_CONFLICT
                        && ! c2_is_decision_var(ca->c2, v->var_id)
                        && skolem_may_depend_on(ca->c2->skolem, lit_to_var(lit), ca->conflicted_var_id),
                        "No reason for lit %d found in conflict analysis.\n", lit);
                //                assert(ca->c2->state == C2_EXAMPLES_CONFLICT && c2_is_decision_var(ca->c2, v->var_id)); // this means it was a decision variable for the example domain
                int_vector_add(ca->conflicting_assignments[copy], lit); // must be decision variable (and conflict caused by this decision)
                //            } else if (!reason->consistent_with_originals) { // decision clause!
                //                assert(c2_is_decision_var(ca->c2, lit_to_var(lit)) || lit_to_var(lit) == ca->conflicted_var_id);
                //                int_vector_add(ca->conflicting_assignment, lit);
            } else if (!legal_reason(ca, lit, reason, copy)) { // TODO: document why
                int_vector_add(ca->conflicting_assignments[copy], lit);
            } else {
                assert(reason->original || reason->consistent_with_originals);
                if (debug_verbosity >= VERBOSITY_HIGH) {
                    V3("  Reason for %d in copy %d is clause %u: ", lit, copy, reason->clause_id);
                    qcnf_print_clause(reason, stdout);
                }
                conflict_analysis_schedule_causing_vars_in_work_queue(ca, reason, lit, copy);
            }
        }
    }
    
    if (ca->c2->options->minimize_conflicts) {
        conflict_analysis_minimize_conflicting_assignment(ca, ca->conflicting_assignments[copy]);
    }
}

void ca_free(conflict_analysis* ca) {
    assert(worklist_count(ca->queue[0]) == 0);
    assert(worklist_count(ca->queue[1]) == 0);
    worklist_free(ca->queue[0]);
    worklist_free(ca->queue[1]);
    int_vector_free(ca->conflicting_assignments[0]);
    int_vector_free(ca->conflicting_assignments[1]);
    free(ca);
}


Clause* conflict_analysis_assignment_to_clause(conflict_analysis* ca, int_vector* assignment) {
    for (unsigned i = 0; i < int_vector_count(assignment); i++) {
        int lit = int_vector_get(assignment, i);
        qcnf_add_lit(ca->c2->qcnf, - lit);
    }
    return qcnf_close_clause(ca->c2->qcnf);
}

// If the clause is not new, go back additional decision levels in the maximal dependency set in this clause.
void conflict_analysis_ensure_constraint_is_new(conflict_analysis* ca, int copy) {
    if (! qcnf_is_new_constraint(ca->c2->qcnf, ca->conflicting_assignments[copy], true)) {
        V1("      ... one more deeper (current length is %d).\n", int_vector_count(ca->conflicting_assignments[copy]));
        // The derived clause is not new, so we didn't actually discover anything new.
        // It looks like we have to follow back some more implications to get a new clause. Reduce the ca-> at least one more level.
        unsigned maximal_dlvl = 0;
        unsigned maximal_scope_id = 0;   assert(ca->c2->qcnf->problem_type != QCNF_DQBF);
        
        for (unsigned i = 0; i < int_vector_count(ca->conflicting_assignments[copy]); i++) {
            Lit lit = int_vector_get(ca->conflicting_assignments[copy], i);
            
            if (qcnf_get_scope(ca->c2->qcnf, lit_to_var(lit)) > maximal_scope_id) {
                maximal_scope_id = qcnf_get_scope(ca->c2->qcnf, lit_to_var(lit));
                maximal_dlvl = 0;
            }
            if (qcnf_get_scope(ca->c2->qcnf, lit_to_var(lit)) == maximal_scope_id) {
                if (ca->domain_get_decision_lvl(ca->domain, lit_to_var(lit)) > maximal_dlvl) {
                    maximal_dlvl = ca->domain_get_decision_lvl(ca->domain, lit_to_var(lit));
                }
            }
        }
        for (unsigned i = 0; i < int_vector_count(ca->conflicting_assignments[copy]); i++) {
            Lit lit = int_vector_get(ca->conflicting_assignments[copy], i);
            if (qcnf_get_scope(ca->c2->qcnf, lit_to_var(lit)) >= maximal_scope_id &&
                ca->domain_get_decision_lvl(ca->domain, lit_to_var(lit)) >= maximal_dlvl) {
                worklist_push(ca->queue[copy], (void*) (int64_t) lit);
                int_vector_remove_index(ca->conflicting_assignments[copy], i);
                i--;
            }
        }
        
        ca->conflict_decision_lvl = maximal_dlvl;
        conflict_analysis_follow_implication_graph(ca, copy);
        abortif(! qcnf_is_new_constraint(ca->c2->qcnf, ca->conflicting_assignments[copy], true), "Constraint is still not new");
    }
}

int_vector* conflict_analysis_resolve_copies(conflict_analysis* ca) {
    
    unsigned var_with_complementary_literals = 0;
    if (ca->c2->qcnf->problem_type != QCNF_2QBF) { // cannot/shouldn't happen in 2QBF
        for (unsigned i = 0 ; i < int_vector_count(ca->conflicting_assignments[0]); i++) {
            Lit l = int_vector_get(ca->conflicting_assignments[0], i);
            if (lit_to_var(l) != ca->conflicted_var_id && int_vector_contains(ca->conflicting_assignments[1], - l)) {
                var_with_complementary_literals = lit_to_var(l);
                break;
            }
        }
    }
    
    if (var_with_complementary_literals) {
        return NULL;
    }
    // Resolve along conflicted var
    int_vector* resolvent = int_vector_init();
    for (unsigned i = 0 ; i < int_vector_count(ca->conflicting_assignments[0]); i++) {
        Lit l = int_vector_get(ca->conflicting_assignments[0], i);
        if (lit_to_var(l) != ca->conflicted_var_id) {
            int_vector_add(resolvent, l);
        }
    }
    for (unsigned i = 0 ; i < int_vector_count(ca->conflicting_assignments[1]); i++) {
        Lit l = int_vector_get(ca->conflicting_assignments[1], i);
        if (lit_to_var(l) != ca->conflicted_var_id) {
            int_vector_add(resolvent, l);
        }
    }
    return resolvent;
}

vector* analyze_assignment_conflict(C2* c2,
                                        unsigned conflicted_var,
                                        Clause* conflicted_clause,
                                        void* domain,
                                        int  (*domain_get_value)(void* domain, Lit lit, bool second_copy),
                                        Clause* (*domain_get_reason)(void* domain, Lit lit, bool second_copy),
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
    ca->conflicting_assignments[0] = int_vector_init();
    ca->conflicting_assignments[1] = int_vector_init();
    ca->queue[0] = worklist_init_unique_computation(qcnf_compare_literals_by_var_id);
    ca->queue[1] = worklist_init_unique_computation(qcnf_compare_literals_by_var_id);
    ca->domain = domain;
    ca->conflicted_clause = conflicted_clause;
    ca->conflicted_var_id = conflicted_var;
    
    
    // Function pointers
    ca->domain_get_value = domain_get_value;
    ca->domain_get_reason = domain_get_reason;
    ca->domain_is_legal_dependence = domain_is_legal_dependence;
    ca->domain_get_decision_lvl = domain_get_decision_lvl;
    
    vector* clauses = vector_init();
    
    if (conflicted_clause) {
        // add literals of conflicted clause to worklist
        ca->conflict_decision_lvl = 0;
        for (unsigned i = 0; i < conflicted_clause->size; i++) {
            Lit l = conflicted_clause->occs[i];
            unsigned var_id = lit_to_var(l);
            assert(var_id == conflicted_var || ca->domain_get_value(ca->domain, l, 0) == -1);
            worklist_push(ca->queue[0], (void*) (int64_t) - l);
            if (domain_get_decision_lvl(domain, var_id) > ca->conflict_decision_lvl) {
                ca->conflict_decision_lvl = domain_get_decision_lvl(domain, var_id);
            }
        }
        conflict_analysis_follow_implication_graph(ca, 0);
        
        Clause* learnt = conflict_analysis_assignment_to_clause(ca, ca->conflicting_assignments[0]);
        abortif(learnt == NULL, "Learning from conflicted clause resulted in duplicate or tautological clause.");
        vector_add(clauses, learnt);
        
    } else {
        assert(conflicted_var != 0);
        ca->conflict_decision_lvl = domain_get_decision_lvl(domain, conflicted_var); // ca->c2->skolem->decision_lvl;
        
        assert(domain_get_value(domain,   (Lit) conflicted_var, 0) == 1);
        assert(domain_get_value(domain, - (Lit) conflicted_var, 1) == 1);
        
        
        worklist_push(ca->queue[0], (void*)   (int64_t) conflicted_var);
        conflict_analysis_follow_implication_graph(ca, 0);
        
        worklist_push(ca->queue[1], (void*) - (int64_t) conflicted_var);
        conflict_analysis_follow_implication_graph(ca, 1);
        
        
        // Add the complementary literals to make both copies proper conflicting assignments
        int_vector_add(ca->conflicting_assignments[0], - (Lit) ca->conflicted_var_id);
        int_vector_add(ca->conflicting_assignments[1],   (Lit) ca->conflicted_var_id);
        
        int_vector* combined_assignment = NULL;// conflict_analysis_resolve_copies(ca);
        
        int next_copy_to_backtrack = 0;
        int itercount = 0;
        while (true) {
            itercount += 1;
            combined_assignment = conflict_analysis_resolve_copies(ca);
            if (combined_assignment == NULL || qcnf_is_new_constraint(ca->c2->qcnf, combined_assignment, true)) {
                break;
            }
            conflict_analysis_ensure_constraint_is_new(ca, next_copy_to_backtrack);
            next_copy_to_backtrack = 1 - next_copy_to_backtrack; // next time use the other copy
            abortif(itercount > 2, "Couldn't resolve this conflict by a new constraint");
        }
        
        if (combined_assignment) {
            assert(qcnf_is_new_constraint(ca->c2->qcnf, combined_assignment, true));
            Clause* learnt = conflict_analysis_assignment_to_clause(ca, combined_assignment);
            abortif(learnt == NULL, "Learning from conflicted variable resulted in duplicate or tautological clause.");
            vector_add(clauses, learnt);
        } else { // complementary literals, cannot resolve clauses along conflicted var; treat separately
            assert(ca->c2->qcnf->problem_type != QCNF_DQBF); // code below may not be general enough for DQBF
            
            for (int copy = 0; copy < 2; copy++) {
                conflict_analysis_ensure_constraint_is_new(ca, copy);
                
                Clause* learnt = conflict_analysis_assignment_to_clause(ca, ca->conflicting_assignments[copy]);
                abortif(learnt == NULL, "Learning from backpropagation conflict resulted in duplicate or tautological clause.");
                vector_add(clauses, learnt);
            }
        }
    }
    
#ifdef DEBUG
    for (unsigned copy = 0; copy < 2; copy++) {
        for (unsigned i = 0; i < int_vector_count(ca->conflicting_assignments[copy]); i++) {
            Lit l_debug = int_vector_get(ca->conflicting_assignments[copy], i);
            Var* v_debug = var_vector_get(c2->qcnf->vars, lit_to_var(l_debug));
            abortif(!v_debug->original, "Conflict clause contains helper variables.\n");
            abortif(int_vector_contains(ca->conflicting_assignments[copy], -l_debug), "Conflict clause contains positive and negative literal.\n");
        }
    }
#endif
    
//    V2("Conflict: ");
//    if (debug_verbosity >= VERBOSITY_MEDIUM) {
//        int_vector_print(ca->conflicting_assignments[0]);
//        int_vector_print(ca->conflicting_assignments[1]);
//    }
    abortif(vector_count(clauses) == 0, "No clauses learnt. Critical error");
    ca_free(ca);
    
    for (unsigned i = 0; i < vector_count(clauses); i++) {
        Clause* c = vector_get(clauses, i);
        c->original = false;
        c->consistent_with_originals = true;
    }
    
    return clauses;
}
