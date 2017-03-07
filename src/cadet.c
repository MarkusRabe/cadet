//
//  incremental_determinization.c
//  caqe
//
//  Created by Markus Rabe on 11/12/15.
//  Copyright © 2015 Saarland University. All rights reserved.
//

#include "cadet.h"
#include "assert.h"
#include "log.h"
#include "parse.h"
#include "certification.h"
#include "util.h"
#include "satsolver.h"

void restart_heuristics(CADET*);
void check_for_unique_consequence(CADET*, MClause*);

CADET* cadet_init_no_matrix(Options* o) {
    CADET* cadet = malloc(sizeof(CADET));
    
    cadet->matrix = NULL;
    cadet->options = o;
    cadet->skolem = satsolver_init();
    cadet->skolem_vars = vector_init();
    
    cadet->state = CADET_READY;
    cadet->result = CADET_RESULT_UNKNOWN;
    cadet->refuting_assignment = NULL;
    cadet->conflict_clause = NULL;
    
    cadet->variables_to_check_for_conflict_analysis = heap_init(compare_variables_by_occ_num);
    cadet->variables_contained_in_conflict_analysis_heap = map_init();
    cadet->conflicted_var = NULL;
    cadet->learnt_clauses_propagation_check_after_backtracking = map_init();
    
    // Statistics
    cadet->deterministic_vars = 0;
    cadet->one_sided_deterministic_vars = 0;
    cadet->symbolic_QBCE_deterministic = 0;
    cadet->determinicity_sat_calls = 0;
    cadet->local_conflict_sat_calls = 0;
    cadet->global_conflict_sat_calls = 0;
    cadet->conflicts = 0;
    cadet->added_clauses = 0;
    cadet->decisions = 0;
    cadet->restarts = 0;
    
    cadet->decision_conflict_timer = statistics_init(10000.0);
    cadet->propagation_conflict_timer = statistics_init(10000.0);
    
    // Magic constants
    cadet->initial_restart = 10; // [1..100] // depends also on restart factor
    cadet->next_restart = cadet->initial_restart;
    cadet->restart_factor = (float) 1.2; // [1.01..2]
    cadet->occurrence_size_weight = (float) 0.2; // [-1..1]
    cadet->conflict_var_weight = 2; // [0..5]
    cadet->conflict_clause_weight = 1; // [0..3]
    cadet->long_clause_death_rate_on_restart_per_literal = (float) 0.05;
    cadet->decision_var_activity_modifier = (float) 0.9; // [-3.0..2.0]
    cadet->small_clause_threshold = 2; // [1..3]
    cadet->decay_rate = (float) 0.9;
    cadet->major_restart_frequency = 20;
    
    return cadet;
}

/*
 * Adds the matrix to the cadet object and adds some finishing touches to the matrix and cadet.
 * 1. We initialize the satsolver with the max_var_id
 * 2.
 *
 * Splitting the matrix initialization off the normal initialization is necessary in case we 
 * want to change the matrix through the cadet interface before solving.
 */
void cadet_init_matrix(CADET* cadet, Matrix* m) {
    
    cadet->matrix = m;
    
    if (m->max_var_id > 0) {
        satsolver_set_max_var(cadet->skolem, m->max_var_id);
    }
    
    for (unsigned j = 0; j < vector_count(m->scopes); j++) {
        MScope* s = vector_get(m->scopes, j);
        if (s->qtype == QUANTIFIER_UNIVERSAL) {
            for (unsigned i = 0; i < vector_count(s->vars); i++) {
                MVar* v = vector_get(s->vars, i);
                vector_add(cadet->skolem_vars, v);
                assert(v->decision_level == NO_DECISION);
            }
        }
    }
    
    // Check all clauses for unique directions
    // Put all variables with occurrennces that are unique directions in the variables_to_check_for_determinicity heap.
    for (MClause* c = cadet->matrix->first_clause; c != NULL; c = c->next) {
        assert(c->unique_consequence_occ == NULL);
        check_for_unique_consequence(cadet, c);
    }
    
    assert((int)cadet->matrix->clause_num - (int)cadet->matrix->satisfied_clauses > 0);
    assert(cadet->matrix->result == MATRIX_UNKNOWN);
}

static inline Occ* is_unit_clause(MClause* c) {
    if (is_clause_satisfied(c)) {
        return NULL;
    }
    Occ* active_occ = NULL;
    for (unsigned j = 0; j < c->size; j++) {
        Occ* o = &c->occs[j];
        if (o->var->value == 0) {
            if (active_occ == NULL) {
                active_occ = o;
            } else {
                return NULL;
            }
        }
    }
    return active_occ;
}

int is_constant(MVar* v) {
    assert(v->value == 0); // is not YET constant
    
    for (unsigned i = 0; i < vector_count(v->pos_occs); i++) {
        Occ* o = vector_get(v->pos_occs, i);
        Occ* implied_occ = is_unit_clause(o->clause);
        if (implied_occ != NULL) {
            assert(implied_occ->var == v && implied_occ == o);
            int val = implied_occ->neg ? -1 : 1;
            V3("MVariable %d is constant.\n", v->var_id);
            return val;
        }
    }
    for (unsigned i = 0; i < vector_count(v->neg_occs); i++) {
        Occ* o = vector_get(v->neg_occs, i);
        Occ* implied_occ = is_unit_clause(o->clause);
        if (implied_occ != NULL) {
            assert(implied_occ->var == v && implied_occ == o);
            int val = implied_occ->neg ? -1 : 1;
            V3("MVariable %d is constant.\n", v->var_id);
            return val;
        }
    }
    return 0;
}

void add_negated_clauses_with_unique_consequence(SATSolver* sat, vector* occurrences) {
    
    int_vector* conjunction_vars = int_vector_init();
    
    for (unsigned i = 0; i < vector_count(occurrences); i++) {
        Occ* o = vector_get(occurrences, i);
        
//        assert(is_active(o)); // can happen if we check for downstream conflicts
        
        if (o->clause->unique_consequence_occ == o) {
            
            Occ* satisfying_occ = is_clause_satisfied(o->clause);
            if (satisfying_occ != NULL && satisfying_occ != o) {  // is_clause_satisfied(o->clause) == o can happen if we check for downstream conflicts
                continue;
            }
            
            int conjunction_var = satsolver_inc_max_var(sat);
            int_vector_add(conjunction_vars, conjunction_var);
            
            for (int j = 0; j < o->clause->size; j++) {
                Occ* clause_occ = &(o->clause->occs[j]);
                if (clause_occ->var->value == 0 &&  clause_occ != o /* && (int) o->var->scope->level >= clause_occ->var->dependence_level*/) {
                    assert(clause_occ->var->dependence_level != NO_DEPENDENCE_LVL
                           || clause_occ->var->scope->qtype == QUANTIFIER_UNIVERSAL
                           || clause_occ->var->scope->level < o->var->scope->level);
                    
                    int lit = clause_occ->neg ? - clause_occ->var->var_id : clause_occ->var->var_id;
                    satsolver_add(sat, - lit);
                    satsolver_add(sat, conjunction_var);
                    satsolver_clause_finished(sat);
                }
            }
        }
    }
    
    for (unsigned i = 0; i < int_vector_count(conjunction_vars); i++) {
        int conjunction_var = int_vector_get(conjunction_vars, i);
        satsolver_add(sat, - conjunction_var);
    }
    satsolver_clause_finished(sat);
    
    int_vector_free(conjunction_vars);
}

void print_skolem_assignment(CADET* cadet, int_vector* additional_assignments) {
    for (unsigned i = 0; i < vector_count(cadet->skolem_vars); i++) {
        MVar* var = vector_get(cadet->skolem_vars, i);
        
        int value = satsolver_deref(cadet->skolem, var->var_id);
        
        // assumptions are not necessarily assigned, as the actual conflict clauses not in this sat solver.
        // TODO: think about adding the variable's determinicity constraints
        if (value == 0 && int_vector_contains_sorted(additional_assignments, var->var_id)) {
            value = 1;
        }
        if (value == 0 && int_vector_contains_sorted(additional_assignments, - var->var_id)) {
            value = -1;
        }
        
        if (value != 0) {
            assert(var->dependence_level != NO_DEPENDENCE_LVL
                   || var->scope->qtype == QUANTIFIER_UNIVERSAL
                   || var->scope->level < var->scope->level);
            assert(! int_vector_contains_sorted(additional_assignments, - value * var->var_id));
//            printf(" %c", var->scope->qtype == QUANTIFIER_UNIVERSAL ? 'a' : 'e');
            printf(" %d", var->var_id * value);
        }
    }
    printf("\n");
}


bool is_clause_satisfied_in_SAT_assignment(CADET* cadet, MClause* clause) {
    for (unsigned i = 0; i < clause->size; i++) {
        Occ* o = &clause->occs[i];
        int val = satsolver_deref(cadet->skolem, o->neg ? - o->var->var_id : o->var->var_id);
        if (val == 1) {
            return true;
        }
    }
    return false;
}

MClause* get_violated_clause(CADET* cadet, vector* occs) {
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Occ* o = vector_get(occs, i);
        if (o->clause->unique_consequence_occ == o && has_illegal_dependence(o->clause)) {
            if (! is_clause_satisfied_in_SAT_assignment(cadet, o->clause)) {
                return o->clause;
            }
        }
    }
    return NULL;
}

MVar* determine_conflicted_var(CADET* cadet, MVar* v) {
    if (v->scope == matrix_get_last_scope(cadet->matrix)) { // no downstream conflicts possible, captures 2QBF
        return v;
    }
    MClause* violated_clause = get_violated_clause(cadet,v->pos_occs);
    if (! violated_clause) {
        violated_clause = get_violated_clause(cadet,v->neg_occs);
    }
    if (violated_clause == NULL) {
        V3("No problem with illegal dependencies found. Returning var %d as cause of the conflict.\n",v->var_id);
        return v;
    }
    Occ* last_occ = &violated_clause->occs[violated_clause->size - 1];
    NOT_IMPLEMENTED(); // test this thing
    return last_occ->var;
}

bool is_var_conflicted(CADET* cadet, MVar* v) {
//    assert(v->value == 0); // can happen when we check for downstream conflicts
    assert(v->scope->qtype == QUANTIFIER_EXISTENTIAL);

    SATSolver* sat = satsolver_init();
    satsolver_set_max_var(sat, cadet->matrix->max_var_id);
    
    add_negated_clauses_with_unique_consequence(sat, v->pos_occs);
    add_negated_clauses_with_unique_consequence(sat, v->neg_occs);
    
    V3("Checking for conflicts for var %d ...", v->var_id);
    
    bool conflict = false;
    
    sat_res result = satsolver_sat(sat);
    cadet->local_conflict_sat_calls++;
    
    if (result == SATSOLVER_SATISFIABLE) {
        V3(" detected local conflict. Starting global conflict check ...\n  ");
        
        satsolver_push(cadet->skolem);
        
        add_negated_clauses_with_unique_consequence(cadet->skolem, v->pos_occs);
        add_negated_clauses_with_unique_consequence(cadet->skolem, v->neg_occs);
        
        sat_res result_global = satsolver_sat(cadet->skolem);
        cadet->global_conflict_sat_calls++;
        
        if (result_global == SATSOLVER_SATISFIABLE) {
            cadet->conflicted_var = determine_conflicted_var(cadet, v); // different from v in case there is a downstream conflict
            cadet->state = CADET_CONFLICT;
            conflict = true;
        } else {
            assert(result_global == SATSOLVER_UNSATISFIABLE);
            satsolver_pop(cadet->skolem);
        }
    } else {
        V3(" no conflict possible.\n");
    }
    
    satsolver_free(sat);
    
    return conflict;
}

//void add_symbolic_QBCE_strengthening(SATSolver* sat, MVar* v, vector* occurrences) {
//    int_vector* conjunction_vars = int_vector_init();
//    
//    for (unsigned i = 0; i < vector_count(occurrences); i++) {
//        Occ* o = vector_get(occurrences, i);
//        
//        assert(is_active(o));
//        assert(   o->clause->unique_consequence_occ == o
//               || o->clause->unique_consequence_occ == NULL
//               || o->clause->unique_consequence_occ->var->scope->level > o->var->scope->level
//               );
//        
//        if (is_clause_satisfied(o->clause)) {
//            continue;
//        }
//        
//        if (o->clause->unique_consequence_occ == NULL || o->clause->unique_consequence_occ->var != v) {
////        if (o->clause->unique_consequence_occ == NULL) {
//            // if (o->clause->blocked_lit == o) {continue;}
//            
//            int conjunction_var = satsolver_inc_max_var(sat); // can be optimized
//            int_vector_add(conjunction_vars, conjunction_var);
//            
//            for (int j = 0; j < o->clause->size; j++) {
//                Occ* clause_occ = &(o->clause->occs[j]);
//                if (is_active(clause_occ)  &&  clause_occ != o  && ( clause_occ->var->scope->qtype == QUANTIFIER_UNIVERSAL  ||  clause_occ->var->dependence_level != UNDECIDED )) {
//                    int lit = clause_occ->var->var_id * (clause_occ->neg ? - 1 : 1);
//                    satsolver_add(sat, - lit);
//                    satsolver_add(sat, conjunction_var);
//                    satsolver_clause_finished(sat);
//                }
//            }
//        }
//    }
//    
//    for (unsigned i = 0; i < int_vector_count(conjunction_vars); i++) {
//        int conjunction_var = int_vector_get(conjunction_vars, i);
//        satsolver_add(sat, - conjunction_var);
//    }
//    satsolver_clause_finished(sat);
//    
//    int_vector_free(conjunction_vars);
//}

bool add_clauses_with_unique_consequence_and_legal_dependence(SATSolver* sat,
                                                              MVar* v,
                                                              vector* occurrences,
                                                              vector* relevant_vars,
                                                              bool skip_v_occurrences) {

    bool occs_all_determined = true;
    assert(relevant_vars == NULL); // deprecated functionality. update the code eventually.
    
    for (unsigned i = 0; i < vector_count(occurrences); i++) {
        Occ* o = vector_get(occurrences, i);
        
        assert(o->var->value == 0);
        assert(   o->clause->unique_consequence_occ == o
               || o->clause->unique_consequence_occ == NULL
               || o->clause->unique_consequence_occ->var->scope->level > o->var->scope->level
               );
        
        if (is_clause_satisfied(o->clause)) {
//            assert(o->clause->unique_consequence_occ == NULL);
            continue;
        }
        
        if (o->clause->unique_consequence_occ == o && ! has_illegal_dependence(o->clause)) {
            // add this clause except o to the sat solver
            for (int j = 0; j < o->clause->size; j++) {
                Occ* clause_occ = &(o->clause->occs[j]);
                bool active = clause_occ->var->value == 0;
                if (active  &&  (!skip_v_occurrences || clause_occ != o) /* && (skip_v_occurrences || (int) o->var->scope->level >= clause_occ->var->dependence_level)*/) {
                    assert(clause_occ->var->dependence_level != NO_DEPENDENCE_LVL
                        || clause_occ->var->scope->qtype == QUANTIFIER_UNIVERSAL
                        || clause_occ->var->scope->level < v->scope->level
                        || ! skip_v_occurrences /*indicates calls by extend_skolem_by_var*/);
                    int lit = clause_occ->neg ? - clause_occ->var->var_id : clause_occ->var->var_id;
                    satsolver_add(sat, lit);
                }
                
                // adds even inactive clauses
                if (clause_occ != o
                    && relevant_vars != NULL
                    && (! skip_v_occurrences ? active : clause_occ->var->dependence_level != NO_DEPENDENCE_LVL)
                    && ! vector_contains(relevant_vars, clause_occ->var)) {
                    vector_add(relevant_vars, clause_occ->var);
                }
            }
            satsolver_clause_finished(sat);
        } else {
            occs_all_determined = false;
        }
    }
    
    return occs_all_determined;
}

static inline bool is_nondeterministic(MVar* v) {
    return v->value == 0 && v->dependence_level == NO_DEPENDENCE_LVL && v->scope->qtype == QUANTIFIER_EXISTENTIAL;
}

void check_for_unique_consequence(CADET* cadet, MClause* c) {
    
    if (c->unique_consequence_occ != NULL) {
        return;
    }
    
    Occ* last_undecided = &c->occs[c->size-1];
    for (; last_undecided >= c->occs; last_undecided--) {
        if (last_undecided->var->value == (last_undecided->neg ? -1 : 1)) {
            return; // clause satisfied
        }
        if (is_nondeterministic(last_undecided->var)) {
            break;
        }
    }

    assert(last_undecided >= c->occs); // means that we have found one
    
//    Occ* last_occ = &c->occs[c->size -1];
//    if (last_undecided->var->scope->level < last_occ->var->scope->level) {
//        // this would be an illegal dependence anyways!
//        return;
//    }
    
    int undecided_lits_num = 1;
    
    for (Occ* o = last_undecided; --o >= c->occs;) {
        if (o->var->value == (o->neg ? -1 : 1)) {
            return; // clause satisfied
        }
        
        if (is_nondeterministic(o->var) ) {
            undecided_lits_num++;
            if (undecided_lits_num >= 2) {
                break;
            }
        }
    }
    
    assert(undecided_lits_num == 0  ||  last_undecided != NULL);
    assert(last_undecided == NULL  ||  last_undecided->var->value == 0 || last_undecided->var->scope->qtype == QUANTIFIER_UNIVERSAL);
    
    if (undecided_lits_num == 1) {
        assert(!is_clause_satisfied(c));
        V3("Assigned clause %d a unique propagation direction", c->clause_id);
        c->unique_consequence_occ = last_undecided;
        
        if (! last_undecided->var->needs_determinicity_check) {
            V3("; queueing variable %d", last_undecided->var->var_id);
            last_undecided->var->needs_determinicity_check = true;
            heap_push(cadet->matrix->variables_to_check_for_determinicity, last_undecided->var);
        }
        V3(".\n");
    }
}


void extend_skolem_by_var(CADET* cadet, MVar* v) {
    assert(v->decision_level == cadet->matrix->decision_level);
    assert(v->dependence_level != NO_DEPENDENCE_LVL && v->dependence_level <= v->scope->level && v->dependence_level >= cadet->matrix->minimal_dependence_lvl);
    add_clauses_with_unique_consequence_and_legal_dependence(cadet->skolem, v, v->pos_occs, NULL, false);
    add_clauses_with_unique_consequence_and_legal_dependence(cadet->skolem, v, v->neg_occs, NULL, false);
}

void make_occ_of_var_directed_occ(MClause* clause, MVar* v) {
    assert(clause->unique_consequence_occ == NULL);
    for (unsigned i = clause->size; i > 0; i--) {
        Occ* o = &clause->occs[i-1];
        if (o->var == v) {
            clause->unique_consequence_occ = o;
        }
    }
    assert(clause->unique_consequence_occ != NULL);
    assert(clause->unique_consequence_occ->var == v);
}

// the unique antecedent is the negated part of the clause that is deterministic already
// The result 0 means TRUE.
int define_unique_antecedent(CADET* cadet, MClause* c) {
    assert(c->size > 0);
    assert(c->unique_consequence_occ != NULL);
    
    if (c->size == 1) {
        return 0; // means true
    } else if (c->size == 2) { // only one _other_ variable in the clause
        for (unsigned j = 0; j < c->size; j++) {
            Occ* o = &c->occs[j];
            if (o != c->unique_consequence_occ) {
                assert(o->var->dependence_level != NO_DEPENDENCE_LVL);
                int res = (o->neg ? 1 : -1) * o->var->var_id;
                assert(res != 0);
                return res;
            }
        }
    } else {
        assert(c->size > 2);
        MVar* conjunction_var = matrix_inc_max_var(cadet->matrix);
        conjunction_var->is_helper = true;
        
        unsigned added = 0;
        for (unsigned j = 0; j < c->size; j++) {
            Occ* clause_occ = &c->occs[j];
            if (clause_occ != c->unique_consequence_occ) {
                assert(clause_occ->var->dependence_level != NO_DEPENDENCE_LVL);
                added++;
                matrix_add_lit_undoable(cadet->matrix, (clause_occ->neg ? 1 : -1) * clause_occ->var->var_id);
                matrix_add_lit_undoable(cadet->matrix, - conjunction_var->var_id);
                MClause* conjunction_clause1 = matrix_add_lit_undoable(cadet->matrix, 0);
                assert(conjunction_clause1);
                cadet->added_clauses++;
                make_occ_of_var_directed_occ(conjunction_clause1, conjunction_var);
                assert(conjunction_clause1->unique_consequence_occ->var == conjunction_var);
                
                if (debug_verbosity >= VERBOSITY_ALL) {
                    V3("Added clause %d: ", conjunction_clause1->clause_id);
                    matrix_print_clause_debug(conjunction_clause1);
                }
            }
        }
        assert(added > 0);
        
        for (unsigned j = 0; j < c->size; j++) {
            Occ* clause_occ = &c->occs[j];
            if (clause_occ != c->unique_consequence_occ) {
                assert(clause_occ->var->dependence_level != NO_DEPENDENCE_LVL);
                matrix_add_lit_undoable(cadet->matrix, (clause_occ->neg ? -1 : 1) * clause_occ->var->var_id);
            }
        }
        matrix_add_lit_undoable(cadet->matrix, conjunction_var->var_id);
        MClause* conjunction_clause2 = matrix_add_lit_undoable(cadet->matrix, 0);
        cadet->added_clauses++;
        assert(conjunction_clause2->size > 1);
        make_occ_of_var_directed_occ(conjunction_clause2, conjunction_var);
        
        if (debug_verbosity >= VERBOSITY_ALL) {
            V3("Added clause %d: ", conjunction_clause2->clause_id);
            matrix_print_clause_debug(conjunction_clause2);
        }
        
        cadet->deterministic_vars++;
        matrix_deterministic_var(cadet->matrix, conjunction_var);
        extend_skolem_by_var(cadet, conjunction_var);
        
        assert(conjunction_var->var_id != 0);
        return conjunction_var->var_id;
    }
    
    abort(); // shouldn't reach this point
}

// Determinise the relation for this variable, fix the remaining cases to have val polarity.
// This operation adds more clauses to the matrix; these should not cause conflicts.
void fix_var_as_remaining_cases_of_occs(CADET* cadet, MVar* v, vector* occs, int polarity, bool one_sided_is_enough) {
    assert(polarity == 1 || polarity == -1);
    assert(v->value == 0);
    
    int_vector* conjunction_vars = int_vector_init();
    
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Occ* o = vector_get(occs, i);
//        assert((o->neg && polarity == 1) || (!o->neg && polarity == -1));
        MClause* c = o->clause;
        assert(!is_clause_satisfied(c));
        int conjunction_lit = define_unique_antecedent(cadet, c);
        if (conjunction_lit != 0) {
            int_vector_add(conjunction_vars, conjunction_lit);
        } else {
            // conjunction_lit is 0, which means that this conjunction lit true,
            // Therefore the variable v can be assigned the negated value.
            // Can cancel everything but one iteration of the final for loop of this function
            matrix_add_lit_undoable(cadet->matrix, - v->var_id * polarity);
            MClause* final_clause_opposite = matrix_add_lit_undoable(cadet->matrix, 0);
            if (debug_verbosity >= VERBOSITY_ALL) {
                V3("Added clause %d: ", final_clause_opposite->clause_id);
                matrix_print_clause_debug(final_clause_opposite);
            }
            
            cadet->added_clauses++;
            assert(final_clause_opposite != NULL);
            
            make_occ_of_var_directed_occ(final_clause_opposite, v);
            int_vector_free(conjunction_vars);
            return;
        }
    }
    
    for (unsigned i = 0; i < int_vector_count(conjunction_vars); i++) {
        matrix_add_lit_undoable(cadet->matrix, int_vector_get(conjunction_vars, i));
    }
    matrix_add_lit_undoable(cadet->matrix, v->var_id * polarity);
    MClause* final_clause = matrix_add_lit_undoable(cadet->matrix, 0);
    if (final_clause) {
        cadet->added_clauses++;
        make_occ_of_var_directed_occ(final_clause, v);
        if (debug_verbosity >= VERBOSITY_ALL) {
            V3("Added clause %d: ", final_clause->clause_id);
            matrix_print_clause_debug(final_clause);
        }
    }
    
    if ( ! one_sided_is_enough) {
        for (unsigned i = 0; i < int_vector_count(conjunction_vars); i++) {
            matrix_add_lit_undoable(cadet->matrix, - int_vector_get(conjunction_vars, i));
            matrix_add_lit_undoable(cadet->matrix, - v->var_id * polarity);
            MClause* final_clause_opposite = matrix_add_lit_undoable(cadet->matrix, 0);
            assert(final_clause_opposite != NULL);
            final_clause_opposite->unconflicting = true;
            cadet->added_clauses++;
            make_occ_of_var_directed_occ(final_clause_opposite, v);
            
            if (debug_verbosity >= VERBOSITY_ALL) {
                V3("Added clause %d: ", final_clause_opposite->clause_id);
                matrix_print_clause_debug(final_clause_opposite);
            }
        }
    }
    
    int_vector_free(conjunction_vars);
}

void fix_remaining_cases(CADET* cadet, MVar* v, int polarity, bool one_sided_is_enough) {
    assert(polarity == 1 || polarity == -1);
    vector* opposite_occs = polarity == 1 ? v->neg_occs : v->pos_occs; // opposite occs
    
    vector* definition_occs = vector_init();
    
    for (unsigned i = 0; i < vector_count(opposite_occs); i++) {
        Occ* o = vector_get(opposite_occs, i);
        if (o->clause->unique_consequence_occ == o && ! is_clause_satisfied(o->clause) && ! has_illegal_dependence(o->clause)) {
            vector_add(definition_occs, o);
        }
    }
    
    fix_var_as_remaining_cases_of_occs(cadet, v, definition_occs, polarity, one_sided_is_enough);
    vector_free(definition_occs);
}

//void fix_defensive_decision(CADET* cadet, MVar* v, int polarity) {
//    assert(polarity == 1 || polarity == -1);
//    
//    MVar* necessary_opposite = matrix_inc_max_var(cadet->matrix);
//    necessary_opposite->is_helper = true;
//    necessary_opposite->needs_determinicity_check = true;
//    heap_push(cadet->matrix->variables_to_check_for_determinicity, necessary_opposite);
//    
//    vector* opposite_occs = polarity == 1 ? v->neg_occs : v->pos_occs; // oposite occs
//    vector* definition_occs = vector_init();
//    
//    for (unsigned i = 0; i < vector_count(opposite_occs); i++) {
//        Occ* o = vector_get(opposite_occs, i);
//        if (o->clause->unique_consequence_occ == o && ! is_clause_satisfied(o->clause)) {
//            vector_add(definition_occs, o);
//        }
//    }
//    fix_var_as_remaining_cases_of_occs(cadet, necessary_opposite, definition_occs, - 1, false);
//    
//    MVar* should_be_same = matrix_inc_max_var(cadet->matrix);
//    should_be_same->is_helper = true;
//    should_be_same->needs_determinicity_check = true;
//    heap_push(cadet->matrix->variables_to_check_for_determinicity, should_be_same);
//    
//    vector* same_occs = polarity == 1 ? v->pos_occs : v->neg_occs; // opposite occs
//    vector_reset(definition_occs);
//    for (unsigned i = 0; i < vector_count(same_occs); i++) {
//        Occ* o = vector_get(same_occs, i);
//        if (! is_clause_satisfied(o->clause)) {
//            vector_add(definition_occs, o);
//        }
//    }
//    fix_var_as_remaining_cases_of_occs(cadet, should_be_same, definition_occs, - 1, false);
//    vector_free(definition_occs);
//    
//    // (necessary_opposite || ! should_be_same) => (- polarity * v)
//    matrix_add_lit_undoable(cadet->matrix, - necessary_opposite->var_id);
//    matrix_add_lit_undoable(cadet->matrix, - polarity * v->var_id);
//    MClause* c1 = matrix_add_lit_undoable(cadet->matrix, 0);
//    if (debug_verbosity >= VERBOSITY_ALL) {
//        V3("Added c1 clause %d: ", c1->clause_id);
//        matrix_print_clause_debug(c1);
//    }
//    
//    matrix_add_lit_undoable(cadet->matrix, should_be_same->var_id);
//    matrix_add_lit_undoable(cadet->matrix, - polarity * v->var_id);
//    MClause* c2 = matrix_add_lit_undoable(cadet->matrix, 0);
//    if (debug_verbosity >= VERBOSITY_ALL) {
//        V3("Added c2 clause %d: ", c2->clause_id);
//        matrix_print_clause_debug(c2);
//    }
//    
//    matrix_add_lit_undoable(cadet->matrix, - should_be_same->var_id);
//    matrix_add_lit_undoable(cadet->matrix, necessary_opposite->var_id);
//    matrix_add_lit_undoable(cadet->matrix, polarity * v->var_id);
//    MClause* c3 = matrix_add_lit_undoable(cadet->matrix, 0);
//    if (debug_verbosity >= VERBOSITY_ALL) {
//        V3("Added c3 clause %d: ", c3->clause_id);
//        matrix_print_clause_debug(c3);
//    }
//}


//int_vector* assignment_satisfies_clauses(int_vector* assignment, vector* occs) {
//
//    int_vector_sort(assignment, compare_integers_natural_order);
//    
//    int_vector* minimized_assignment = int_vector_init();
//    
//    for (unsigned i = 0; i < vector_count(occs); i++) {
//        Occ* o = vector_get(occs, i);
//        MClause* c = o->clause;
//        Occ* satisfying_occ = NULL;
//        Occ* undetermined_occ = NULL;
//        bool satisfying_occ_in_minimized = false;
//        for (unsigned j = 0; j < c->size; j++) {
//            Occ* clause_occ = &c->occs[j];
//            if (clause_occ->var->dependence_level == NO_DEPENDENCE_LVL) {
//                undetermined_occ = clause_occ;
//                continue;
//            }
//            
//            int lit = clause_occ->var->var_id * (clause_occ->neg ? -1 : 1);
//            assert(!satisfying_occ_in_minimized);
//            
//            if (int_vector_contains_sorted(minimized_assignment, lit)) {
//                satisfying_occ = clause_occ;
//                satisfying_occ_in_minimized = true;
//                break;
//            } else {
//                if (satisfying_occ == NULL) {
//                    if (int_vector_contains_sorted(assignment, lit)) {
//                        satisfying_occ = clause_occ;
//                    }
//                }
//            }
//        }
//        if (satisfying_occ == NULL) {
//            int_vector_free(minimized_assignment);
//            return NULL;
//        }
//        if (! satisfying_occ_in_minimized) {
//            int lit = satisfying_occ->var->var_id * (satisfying_occ->neg ? -1 : 1);
//            int_vector_add_sorted(minimized_assignment, lit);
//        }
//    }
//    return minimized_assignment;
//}

bool contains_nondeterministic_dependence(MVar* v, vector* occs) {
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Occ* o = vector_get(occs, i);
        for (unsigned j = 0; j < o->clause->size; j++) {
            Occ* clause_occ = &o->clause->occs[j];
            if (is_nondeterministic(clause_occ->var) && clause_occ->var->scope->level < v->scope->level) {
                return true;
            }
        }
    }
    return false;
}

bool is_var_deterministic(CADET* cadet, MVar* v) {
    assert(v->value == 0);
    assert(v->dependence_level == NO_DEPENDENCE_LVL);
    assert(v->scope->qtype == QUANTIFIER_EXISTENTIAL);
    
//    if (contains_nondeterministic_dependence(v, v->pos_occs) || contains_nondeterministic_dependence(v, v->neg_occs)) {
//        return false;
//    }
    
    SATSolver* sat = satsolver_init();
    satsolver_set_max_var(sat, cadet->matrix->max_var_id);
    
    bool pos_occs_all_determined = add_clauses_with_unique_consequence_and_legal_dependence(sat, v, v->pos_occs, NULL, true);
    bool neg_occs_all_determined = add_clauses_with_unique_consequence_and_legal_dependence(sat, v, v->neg_occs, NULL, true);
    
    V3("Checking determinicity of var %d via SAT ... ", v->var_id);
    
    int result = satsolver_sat(sat);
    cadet->determinicity_sat_calls++;
    
    bool is_deterministic = false;
    if (result == SATSOLVER_SATISFIABLE) {
        V3("not (yet) deterministic.\n");
        
        assert( ! v->is_decision_var || ! pos_occs_all_determined);
        assert( ! v->is_decision_var || ! neg_occs_all_determined);
        
        if (pos_occs_all_determined || neg_occs_all_determined) {
            V3("Detected var %d as pure literal.\n", v->var_id);
            is_deterministic = true;
            cadet->one_sided_deterministic_vars++;
            
            fix_remaining_cases(cadet, v, pos_occs_all_determined ? -1 : 1, true);
        } else {
//            satsolver_push(sat);
//            add_symbolic_QBCE_strengthening(sat, v, v->pos_occs);
//            
//            result = satsolver_sat(sat);
//            if (result == SATSOLVER_UNSATISFIABLE) {
////                fix_remaining_cases(cadet, v, vector_count(v->pos_occs) < vector_count(v->neg_occs) ? 1 : -1, true);
//                fix_remaining_cases(cadet, v, -1, true);
//                is_deterministic = true;
//            } else {
//                satsolver_pop(sat);
//                add_symbolic_QBCE_strengthening(sat, v, v->neg_occs);
//                
//                result = satsolver_sat(sat);
//                if (result == SATSOLVER_UNSATISFIABLE) {
//                    fix_remaining_cases(cadet, v, 1, true);
//                    is_deterministic = true;
//                }
//            }
        }
    } else {
        V3("MVar %d is deterministic!\n", v->var_id);
        is_deterministic = true;
    }
    
    satsolver_free(sat);
    
    return is_deterministic;
}

void check_clauses_after_determinizing_var(CADET* cadet, MVar* v) {
    // check which clauses get a direction, and put variables in the variable_to_check heap when they may be determinized by this
    for (unsigned i = 0; i < vector_count(v->pos_occs); i++) {
        Occ* o = vector_get(v->pos_occs, i);
        check_for_unique_consequence(cadet, o->clause);
    }
    
    for (unsigned i = 0; i < vector_count(v->neg_occs); i++) {
        Occ* o = vector_get(v->neg_occs, i);
        check_for_unique_consequence(cadet, o->clause);
    }
}

void schedule_unit_clauses(CADET* cadet, vector* occs) {
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Occ* defining_occ = vector_get(occs, i);
        MClause* c = defining_occ->clause;
        Occ* implied = is_unit_clause(c);
        if (implied != NULL && implied->var->scope->qtype == QUANTIFIER_EXISTENTIAL && implied->var->dependence_level == NO_DEPENDENCE_LVL && ! implied->var->needs_determinicity_check) {
            V3("Detected variable %d to be deterministic; scheduled determinicity check.\n", implied->var->var_id);
            assert(! implied->var->is_helper);
            implied->var->needs_determinicity_check = true;
            heap_push(cadet->matrix->variables_to_check_for_determinicity, implied->var);
        }
    }
}

void trigger_determinicity_checks_after_satisfying_clauses(CADET* cadet, vector* occs) {
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Occ* clause_occ = vector_get(occs, i);
        assert(is_clause_satisfied(clause_occ->clause));
        assert(clause_occ->clause->unique_consequence_occ == NULL || clause_occ->clause->unique_consequence_occ == clause_occ || clause_occ->var->scope->level < clause_occ->clause->unique_consequence_occ->var->scope->level);
        for (unsigned j = 0; j < clause_occ->clause->size; j++) {
            Occ* o = &clause_occ->clause->occs[j];
            if (o->var->value == 0 && o->var->scope->qtype == QUANTIFIER_EXISTENTIAL && o->var->dependence_level == NO_DEPENDENCE_LVL && ! o->var->needs_determinicity_check) {
                o->var->needs_determinicity_check = true;
                heap_push(cadet->matrix->variables_to_check_for_determinicity, o->var);
                V3("Scheduled var %d for determinicity check after var %d satisfied a clause.\n",o->var->var_id, clause_occ->var->var_id);
            }
        }
    }
}

//bool all_deterministic(MClause* clause) {
//    for (unsigned i = 0; i < clause->size; i++) {
//        Occ* o = &clause->occs[i];
//        if (is_nondeterministic(o->var)) {
//            return false;
//        }
//    }
//    return true;
//}
//
//
//void get_lower_lvl_implied_vars_that_are_deterministic(CADET* cadet, vector* occs, vector* downstream_implied_vars) {
//    for (unsigned i = 0; i < vector_count(occs); i++) {
//        Occ* o = vector_get(occs, i);
//        if (o->clause->unique_consequence_occ == NULL && all_deterministic(o->clause)) {
//            Occ* new_unique_consequence = &o->clause->occs[o->clause->size - 1];
//            vector_add(downstream_implied_vars, new_unique_consequence->var);
//            o->clause->unique_consequence_occ = new_unique_consequence;
//        }
//    }
//}
//
//bool causes_downstream_conflicts(CADET* cadet, MVar* v) {
//    if (matrix_get_last_scope(cadet->matrix) == v->scope) { // applies to all existential in 2QBF avoiding overhead
//        return false;
//    }
//    
//    // collect the variables of lower levels that now have new clauses with unique consequences.
//    vector* downstream_implied_vars = vector_init();
//    get_lower_lvl_implied_vars_that_are_deterministic(cadet, v->pos_occs, downstream_implied_vars);
//    get_lower_lvl_implied_vars_that_are_deterministic(cadet, v->neg_occs, downstream_implied_vars);
//    vector_sort(downstream_implied_vars);
//    vector_remove_duplicates(downstream_implied_vars);
//    
//    bool conflict = false;
//    for (unsigned i = 0; i < vector_count(downstream_implied_vars); i++) {
//        MVar* downstream_var = vector_get(downstream_implied_vars, i);
//        if (is_var_conflicted(cadet, downstream_var)) {
//            cadet->conflicted_var = downstream_var;
//            conflict = true;
//        }
//    }
//    vector_free(downstream_implied_vars);
//    return conflict;
//}

void propagate(CADET* cadet) {
    
    assert(cadet->state == CADET_READY);
    
    if (debug_verbosity >= VERBOSITY_HIGH) {
        matrix_validate(cadet->matrix);
    }
    
    // this loop triggers checks for learnt clauses after restarts. Captures the case that a learnt clause extends a previous decision level.
    for (MClause* c = cadet->matrix->first_clause; c != NULL; c = c->next) {
        if (!c->learnt) {
            break;
        }
        
        int backtracking_level = (int) map_get(cadet->learnt_clauses_propagation_check_after_backtracking, c->clause_id);
        V3("MClause %d has backtracking level %d.\n", c->clause_id, backtracking_level);
        if (backtracking_level > cadet->matrix->decision_level) {
            map_update(cadet->learnt_clauses_propagation_check_after_backtracking, c->clause_id, (void*) (size_t) cadet->matrix->decision_level);
            
            check_for_unique_consequence(cadet, c);
            
            if (c->unique_consequence_occ != NULL && c->unique_consequence_occ->var->dependence_level == NO_DEPENDENCE_LVL && ! c->unique_consequence_occ->var->needs_determinicity_check) {
                c->unique_consequence_occ->var->needs_determinicity_check = true;
                heap_push(cadet->matrix->variables_to_check_for_determinicity, c->unique_consequence_occ->var);
            }
        } else {
            break;
        }
    }
    
    while (heap_count(cadet->matrix->variables_to_check_for_determinicity) > 0) {
        MVar* v = heap_pop(cadet->matrix->variables_to_check_for_determinicity);
        
        assert(v->needs_determinicity_check);
        v->needs_determinicity_check = false;
        
        if (is_var_deterministic(cadet, v)) {

            matrix_deterministic_var(cadet->matrix, v); // made deterministic before the conflict test to assert that, in case of a conflict, the conflict analysis has an easier time to find the reasons.
            
            if (is_var_conflicted(cadet, v)) {
                assert(cadet->conflicted_var);
                assert(cadet->state == CADET_CONFLICT);
                if (cadet->conflicted_var != v) {
                    NOT_IMPLEMENTED();
                    // TODO: how do we make sure the conflict analysis has a correct value for v, otherwise it cannot find a reason for the conflict in cadet->conflicted_var.
                }
                
                break;
            }
            
            cadet->deterministic_vars++;
            
            extend_skolem_by_var(cadet, v);
            
            int val = is_constant(v);
            if (val != 0) {
                V3("Detected variable %d as constant!\n", v->var_id);
                matrix_assume(cadet->matrix, val, v);
                if (val == 1) {
                    schedule_unit_clauses(cadet, v->neg_occs);
                    trigger_determinicity_checks_after_satisfying_clauses(cadet, v->pos_occs);
                } else {
                    schedule_unit_clauses(cadet, v->pos_occs);
                    trigger_determinicity_checks_after_satisfying_clauses(cadet, v->neg_occs);
                }
            }
            
            check_clauses_after_determinizing_var(cadet, v);
            
        } else {
            assert(! v->is_decision_var);
        }
    }
}

// fixes the __remaining__ cases to be value
void decision(CADET* cadet, MVar* v, int value) {
    V2("Decision for %d\n", v->var_id);
    assert(v->value == 0);
    assert(value == 1 || value == -1);
    cadet->decisions++;
    cadet->deterministic_vars++;
    
    matrix_push_milestone(cadet->matrix);
    satsolver_push(cadet->skolem);
    
    matrix_decision_var(cadet->matrix, v);
    
    fix_remaining_cases(cadet, v, value, false);
//    fix_defensive_decision(cadet, v, value);

    assert(!v->needs_determinicity_check);
    v->needs_determinicity_check = true;
    heap_push(cadet->matrix->variables_to_check_for_determinicity, v);
}

// Returns NULL, if all variables are decided
MVar* pick_most_active_variable(CADET* cadet) {
    MVar* decision_var = NULL;
    
    for (unsigned j = 0; j < vector_count(cadet->matrix->scopes); j += 2) {
        MScope* s = vector_get(cadet->matrix->scopes, j);
        assert(s->qtype== QUANTIFIER_EXISTENTIAL);
        for (unsigned i = 0; i < vector_count(s->vars); i++) {
            MVar* v = vector_get(s->vars, i);
            
            if (v->scope->qtype == QUANTIFIER_EXISTENTIAL) {
                v->activity *= cadet->decay_rate;
            }
            assert(v->value == 0 || v->dependence_level != NO_DEPENDENCE_LVL || (vector_count(v->pos_occs) == 0 && vector_count(v->neg_occs) == 0));
            
            if (is_nondeterministic(v)) { // v->dependence_level == UNDECIDED && v->value == 0 && v->scope->qtype == QUANTIFIER_EXISTENTIAL
                if (decision_var == NULL || decision_var->activity < v->activity) {
                    decision_var = v;
                }
            }
        }
        if (decision_var) {
            break;
        }
    }
    return decision_var;
}

void schedule_causing_vars_in_work_queue(CADET* cadet, MVar* caused, int value, MClause* reason) {
    for (unsigned j = 0; j < reason->size; j++) {
        Occ* o = &reason->occs[j];
        assert(caused == NULL || o->var->dependence_level <= caused->dependence_level);
        
        if (o == reason->unique_consequence_occ) {
            assert(caused != NULL);
            assert(o->var == caused);
            assert(o->neg ? value == -1 : value == 1);
            continue;
        }
        if (! map_contains(cadet->variables_contained_in_conflict_analysis_heap, o->var->var_id)) {
            map_add(cadet->variables_contained_in_conflict_analysis_heap, o->var->var_id, NULL);
            heap_push(cadet->variables_to_check_for_conflict_analysis, o->var);
        }
    }
}

MClause* find_reason_for_value(CADET* cadet, MVar* v, int value) {
    assert(value == 1 || value == -1);
    vector* occs = value == 1 ? v->pos_occs : v->neg_occs;
    
    MClause* candidate = NULL;
    unsigned candidate_quality = 4000000000;
    
//    for (unsigned i = vector_count(occs); i > 0 ; i--) {
//        Occ* var_occ = vector_get(occs, i-1);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Occ* var_occ = vector_get(occs, i);
        MClause* c = var_occ->clause;
        if (c->unique_consequence_occ == NULL || c->unique_consequence_occ->var != v) {
            continue;
        }
        
        bool clause_satisfied_by_other = false;
        for (unsigned j = 0; j < c->size; j++) {
            Occ* o = &c->occs[j];
            assert(o->var->dependence_level <= v->dependence_level);
            
            if (o == c->unique_consequence_occ) {
                assert(o->var == v);
                assert(o->neg ? value == -1 : value == 1);
                continue;
            }
            
            int satval = satsolver_deref(cadet->skolem, o->var->var_id);
            assert(satval == 1 || satval == -1); // this is not actually required; we could modify the if statement below
            if (o->neg ? satval == -1 : satval == 1) {
                clause_satisfied_by_other = true;
                break;
            }
        }
        if (! clause_satisfied_by_other) {
            // is a possible explanation
            if (cadet->options->find_smallest_reason && ! (v->is_decision_var && v->decision_level == cadet->matrix->decision_level && cadet->conflicted_var == v)) { // for decision vars the conflict must already occur for the non-decision clauses, which occur in the beginning of the occurrence list.
                unsigned quality = 0; // small qualities are good
                // determine quality of candidate
                for (unsigned j = 0; j < c->size; j++) {
                    Occ* o = &c->occs[j];
                    if (o != c->unique_consequence_occ && ! map_contains(cadet->variables_contained_in_conflict_analysis_heap, o->var->var_id)) {
                        quality++;
                    }
                }
                if (candidate == NULL) {
                    candidate = c;
                    candidate_quality = quality;
                } else if (quality < candidate_quality) {  // can fix the issue by && (c->learnt || c->original)
//                    matrix_print_debug(cadet->matrix);
                    assert(is_clause_satisfied(c) == NULL || is_clause_satisfied(c) == c->unique_consequence_occ);
                    candidate = c;
                    candidate_quality = quality;
                } else {
                    continue;
                }
                if (quality <= 1) {
                    break;
                }
            } else {
                return c;
            }
        }
    }
    return candidate;
}

int_vector* follow_implication_graph(CADET* cadet) {
    int_vector* conflicting_assignment_of_last_decision_level = int_vector_init();
    while (heap_count(cadet->variables_to_check_for_conflict_analysis) > 0) {
        MVar* v = heap_pop(cadet->variables_to_check_for_conflict_analysis);
        
        assert(v->decision_level <= cadet->matrix->decision_level);
        
        int satval = satsolver_deref(cadet->skolem, v->var_id);
        assert(satval == 1 || satval == -1);
        
        MClause* reason = NULL;
        if (v->scope->qtype == QUANTIFIER_EXISTENTIAL) {
            reason = find_reason_for_value(cadet, v, satval);
            if (reason == NULL) {
                V0("Error while computing the implication graph."
                   " Skolem function seems to be not a circuit.\n");
                abort();
            }
        }
        
        bool is_relevant_decision = false;
        if (v->is_decision_var) {
            // it could still be that the value of the decision var was not forced by the decision, but actually was forced by one of the original or learnt clauses.
            is_relevant_decision = ! reason->original && ! reason->learnt;
        }
        
        if (v->decision_level < cadet->matrix->decision_level || is_relevant_decision || v->scope->qtype == QUANTIFIER_UNIVERSAL) {
            assert(cadet->matrix->decision_level > 1 || v->scope->qtype == QUANTIFIER_UNIVERSAL); // if there was a decision, the decision level should be 2 or higher
//            matrix_add_lit(cadet->matrix, - v->var_id * satval);
            int_vector_add(conflicting_assignment_of_last_decision_level, v->var_id * satval);
        } else {
            assert(v->scope->qtype == QUANTIFIER_EXISTENTIAL);
            assert(reason != NULL);
            schedule_causing_vars_in_work_queue(cadet, v, satval, reason);
        }
    } // end while
    
    return conflicting_assignment_of_last_decision_level;
}

int_vector* cadet_compute_refuting_assignment(CADET* cadet, int_vector* conflict) {
    
    assert(conflict != NULL);
    assert(cadet->state == CADET_CONFLICT);
    assert(heap_count(cadet->variables_to_check_for_conflict_analysis) == 0);
    assert(map_count(cadet->variables_contained_in_conflict_analysis_heap) == 0);
    
    V3("Computing small refuting assignment from conflict clause.\n");
    
    for (unsigned i = 0; i < int_vector_count(conflict); i++) {
        int lit = int_vector_get(conflict, i);
        if (! map_contains(cadet->variables_contained_in_conflict_analysis_heap, (int) lit_to_var(lit))) {
            map_add(cadet->variables_contained_in_conflict_analysis_heap, (int) lit_to_var(lit), NULL);
            MVar* var = map_get(cadet->matrix->var_lookup, (int) lit_to_var(lit));
            heap_push(cadet->variables_to_check_for_conflict_analysis, var);
        }
    }
    
    int current_decision_level = cadet->matrix->decision_level;
    cadet->matrix->decision_level = 1;
    
    int_vector* refuting_assignment = follow_implication_graph(cadet);
    
//    int_vector_sort(refuting_assignment, compare_integers_natural_order);
//    int_vector_remove_duplicates(refuting_assignment);
//    int_vector_sort(refuting_assignment, compare_integers_abs);
    
    cadet->matrix->decision_level = current_decision_level;
    
    assert(heap_count(cadet->variables_to_check_for_conflict_analysis) == 0);
    map_reset(cadet->variables_contained_in_conflict_analysis_heap);
    
    return refuting_assignment;
}


int_vector* cadet_conflict_analysis(CADET* cadet, MVar* conflicted_var) {
    assert(conflicted_var->decision_level <= cadet->matrix->decision_level);
    assert(cadet->state == CADET_CONFLICT);
    assert(heap_count(cadet->variables_to_check_for_conflict_analysis) == 0);
    assert(map_count(cadet->variables_contained_in_conflict_analysis_heap) == 0);
    
    V3("Computing conflict clause.\n");
    
    // find reasons for positive assignment
    MClause* reason_pos = find_reason_for_value(cadet, conflicted_var, 1);
    assert(reason_pos != NULL);
    schedule_causing_vars_in_work_queue(cadet, conflicted_var, 1, reason_pos);
    
    // find reasons for negative assignment
    MClause* reason_neg = find_reason_for_value(cadet, conflicted_var, -1);
    assert(reason_neg != NULL);
    schedule_causing_vars_in_work_queue(cadet, conflicted_var, -1, reason_neg);
    
    int_vector* conflicting_assignment = follow_implication_graph(cadet);
    
    assert(heap_count(cadet->variables_to_check_for_conflict_analysis) == 0);
    map_reset(cadet->variables_contained_in_conflict_analysis_heap);
    
    return conflicting_assignment;
}

void restart_heuristics(CADET* cadet) {
    cadet->next_restart = (unsigned) (cadet->next_restart * cadet->restart_factor);
    
    if (cadet->restarts % cadet->major_restart_frequency == cadet->major_restart_frequency - 1) {
        for (unsigned j = 0; j < vector_count(cadet->matrix->scopes); j++) {
            MScope* s = vector_get(cadet->matrix->scopes, j);
            if (s->qtype == QUANTIFIER_EXISTENTIAL) {
                for (unsigned i = 0; i < vector_count(s->vars); i++) {
                    MVar* v = vector_get(s->vars, i);
                    v->activity = 0;
                }
            }
        }
    } else {
        for (unsigned j = 0; j < vector_count(cadet->matrix->scopes); j++) {
            MScope* s = vector_get(cadet->matrix->scopes, j);
            if (s->qtype == QUANTIFIER_EXISTENTIAL) {
                for (unsigned i = 0; i < vector_count(s->vars); i++) {
                    MVar* v = vector_get(s->vars, i);
                    v->activity = v->activity / (1 + cadet->occurrence_size_weight * (vector_count(v->pos_occs) + vector_count(v->neg_occs)));
                    v->activity += ((float) (rand() % 128)) * 0.002;
                }
            }
        }
    }
    
    if (cadet->options->delete_clauses_on_restarts) {
        MClause* next = NULL;
        for (MClause* c = cadet->matrix->first_clause ; c != NULL && ! c->original; c = next) {
            next = c->next;
            if (c->size > cadet->small_clause_threshold && c->learnt) {
                int chance_to_die = (int)/*rounding happens here*/ (cadet->long_clause_death_rate_on_restart_per_literal * (c->size - cadet->small_clause_threshold));
                if (rand() % 100 < chance_to_die) {
                    matrix_remove_clause(cadet->matrix, c);
                }
            }
        }
    }
}

void conflict_heuristics(CADET* cadet, MClause* conflict) {
    
    for (int i = 0; i < conflict->size; i++) {
        Occ* o = &conflict->occs[i];
        o->var->activity += cadet->conflict_clause_weight;
    }
    cadet->conflicted_var->activity += cadet->conflict_var_weight;
}

cadet_res cadet_run(CADET* cadet) {
    
    assert(cadet->state == CADET_READY);
    
    while (true) {
        
        if (debug_verbosity >= VERBOSITY_ALL) {
            matrix_print_debug(cadet->matrix);
        }
        
        propagate(cadet);
        
        if (debug_verbosity >= VERBOSITY_HIGH) {
            matrix_validate(cadet->matrix);
        }
        
        if (cadet->state != CADET_CONFLICT) {
            
            // pic a variable to take a decision
//            MVar* decision_var = pick_first_decision_variable(cadet);
            MVar* decision_var = pick_most_active_variable(cadet);
//            MVar* decision_var = pick_most_common_decision_variable(cadet);
            
            if (decision_var == NULL) {
                assert(cadet->result == CADET_RESULT_UNKNOWN);
                cadet->result = CADET_RESULT_SAT;
                break;
            }
            
            decision_var->activity *= cadet->decision_var_activity_modifier;
            
            assert(! decision_var->is_helper);
            
            // Fix a decision
            decision(cadet, decision_var, 1); // vector_count(decision_var->pos_occs) < vector_count(decision_var->neg_occs) ? 1 : -1
            
        } else {
            if (cadet->state == CADET_CONFLICT) {
                
                cadet->conflicts += 1;
                
                if (cadet->conflicts >= cadet->next_restart) {
                    assert(cadet->conflicts == cadet->next_restart);
                    
                    cadet->state = CADET_READY;
                    cadet->restarts++;
                    V2("Restart %zu\n", cadet->restarts);
                    
                    restart_heuristics(cadet);
                    
                    satsolver_pop(cadet->skolem); // to compensate the global conflict test
                    
                    while (cadet->matrix->decision_level > 1) {
                        matrix_pop_milestone(cadet->matrix);
                        satsolver_pop(cadet->skolem);
                    }
                    
                    return CADET_RESULT_UNKNOWN;
                }
                
                assert(cadet->matrix->push_count >= cadet->matrix->decision_level - 1);
                
                int_vector* conflict = cadet_conflict_analysis(cadet, cadet->conflicted_var);
                
                V2("Conflict clause: ");
                if (debug_verbosity >= VERBOSITY_MEDIUM) {
                    int_vector_print(conflict);
                }
                
                // determine largest decision level
                int largest_decision_level_involved = 0;
                for (unsigned i = 0; i < int_vector_count(conflict); i++) {
                    int lit = int_vector_get(conflict, i);
                    MVar* var = map_get(cadet->matrix->var_lookup, (int) lit_to_var(lit));
                    if (var->decision_level > largest_decision_level_involved) {
                        largest_decision_level_involved = var->decision_level;
                    }
                    if (largest_decision_level_involved == cadet->matrix->decision_level) {
                        break;
                    }
                }
                
                //////////////////// transfered knowledge from C2. Untested.
                int largest_lvl = 1;
                int second_largest_lvl = 1;
                for (unsigned i = 0; i < int_vector_count(conflict); i++) {
                    Lit lit = int_vector_get(conflict, i);
                    MVar* var = map_get(cadet->matrix->var_lookup, (int) lit_to_var(lit));
                    if (var->decision_level > largest_lvl) {
                        second_largest_lvl = largest_lvl;
                        largest_lvl = var->decision_level;
                    }
                    if (largest_lvl == cadet->matrix->decision_level) {
                        break;
                    }
                }
                assert(largest_lvl == largest_decision_level_involved);
                assert(largest_lvl == 0 || second_largest_lvl < largest_lvl);
                assert(largest_lvl <= cadet->matrix->decision_level);
                /////////////////////
                
                if (largest_decision_level_involved > 1) { /* decisions involved? */
                    
                    satsolver_pop(cadet->skolem);
                    
                    assert(second_largest_lvl < largest_decision_level_involved);
                    // backtrack to largest involved decision level
                    while (second_largest_lvl + 1 <= cadet->matrix->decision_level) { // largest_decision_level_involved 
                        matrix_pop_milestone(cadet->matrix);
                        satsolver_pop(cadet->skolem);
                    }
                    
                    for (unsigned i = 0; i < int_vector_count(conflict); i++) {
                        int lit = int_vector_get(conflict, i);
                        matrix_add_lit(cadet->matrix, - lit);
                    }
                    cadet->conflict_clause = matrix_add_lit(cadet->matrix, 0);
                    assert(cadet->conflict_clause != NULL);
                    cadet->conflict_clause->learnt = true;
                    check_for_unique_consequence(cadet, cadet->conflict_clause);
                    
                    map_add(cadet->learnt_clauses_propagation_check_after_backtracking, cadet->conflict_clause->clause_id, (void*) (size_t) largest_decision_level_involved);
                    
                    conflict_heuristics(cadet, cadet->conflict_clause);
                    
                    cadet->state = CADET_READY;
                    cadet->conflicted_var = NULL;
                    
                } else { // actual conflict
                    
                    int_vector* refuting_assignment = cadet_compute_refuting_assignment(cadet, conflict);
                    cadet->refuting_assignment = refuting_assignment;
                    
                    if (debug_verbosity >= VERBOSITY_MEDIUM) {
                        int_vector_print(refuting_assignment);
                    }
                    
                    if (debug_verbosity >= VERBOSITY_MEDIUM) {
                        V3("Refuting assignment:");
                        int_vector* empty = int_vector_init();
                        print_skolem_assignment(cadet, empty);
                        int_vector_free(empty);
                    }
                    
                    satsolver_pop(cadet->skolem); // compensates push from conflict check
                    
                    assert(cadet->result == CADET_RESULT_UNKNOWN);
                    cadet->result = CADET_RESULT_UNSAT;
                    break;
                }
            }
        }
    }
    return cadet->result;
}










//////////////////////////////////////////////////////////////
//                      Interface                           //
//////////////////////////////////////////////////////////////


void cadet_print_statistics(CADET* cadet) {
    // Creating statistics
    unsigned existential_var_count = 0;
    // Watch out, counting from level two onwards!
    for (unsigned i = 2; i < vector_count(cadet->matrix->scopes); i += 2) {
        MScope* s = vector_get(cadet->matrix->scopes, i);
        assert(s->qtype == QUANTIFIER_EXISTENTIAL);
        
        for (unsigned j = 0; j < vector_count(s->vars); j++) {
            MVar* v = vector_get(s->vars, j);
            if (v->value == 0) {
                existential_var_count++;
            }
        }
    }
    
    unsigned function_clause_count = 0;
    unsigned non_satisfied_clause_count = 0;
    for (MClause* c = cadet->matrix->first_clause; c != NULL; c = c->next) {
        function_clause_count += c->unique_consequence_occ != NULL && c->unique_consequence_occ->var->dependence_level != NO_DEPENDENCE_LVL ? 1 : 0;
        non_satisfied_clause_count += is_clause_satisfied(c) ? 0 : 1;
    }
    
    MScope* first_scope = vector_get(cadet->matrix->scopes, 0);
    V1("Quantifier levels: %u\n", vector_count(cadet->matrix->scopes) - (vector_count(first_scope->vars) == 0 ? 1 : 0));
    V1("Total number of (remaining) existential variables: %u\n", existential_var_count);
    V1("Number of determinizations: %zu\n", cadet->deterministic_vars);
    V1("Number of determinizations by one-sided rule: %zu\n", cadet->one_sided_deterministic_vars);
    V1("Number of SAT calls for determinicity checks: %zu\n", cadet->determinicity_sat_calls);
    V1("Number of SAT calls for local conflict checks: %zu\n", cadet->local_conflict_sat_calls);
    V1("Number of SAT calls for global conflict checks: %zu\n", cadet->global_conflict_sat_calls);
    V1("Number of added clauses: %zu\n", cadet->added_clauses);
    V1("Number of decisions: %zu\n", cadet->decisions);
    V1("Number of conflicts: %zu\n", cadet->conflicts);
    V1("Number of restarts:  %zu\n", cadet->restarts);
    
    //    printf("Propagation conflicts:\n");
    //    statistics_print(cadet->propagation_conflict_timer);
    //    printf("Decision conflicts:\n");
    //    statistics_print(cadet->decision_conflict_timer);
}

int cadet_solve_qdimacs(FILE* f, Options* options) {
    Matrix* m = create_matrix_from_qdimacs(f);
    fclose(f);
    if (!m) {
        V0("Error while reading qdimacs file for simplification.\n");
        return 1;
    }
    
    V0("Number of clauses: %zu\n", m->clause_num);
    
    if (options->preprocess) {
        matrix_simplify(m);
    }
    
    if (options->print_qdimacs) {
        matrix_print_qdimacs(m);
        return 0;
    }
    
    if (m->result == MATRIX_SATISFIABLE) {
        V0("SAT\n");
        return 10;
    }
    if (m->result == MATRIX_UNSATISFIABLE) {
        V0("UNSAT\n");
        return 20;
    }
    
    if (options->preprocess) {
        Matrix* new = matrix_cleanup(m);
        V1("Simplify deleted %d clauses.\n",
           (int)m->clause_num - (int)new->clause_num);
        matrix_free(m);
        m = new;
    }
    
    //////// DEBUG CODE: DEACTIVATING ANALYSIS OF != 2QBF
    MScope* first_scope = vector_get(m->scopes, 0);
    if (vector_count(first_scope->vars) > 0 || vector_count(m->scopes) > 3) {
        return 30;
    }
    ////////
    
    //    matrix_qbce_vars(m);
    //    V1("QBCE detected %zu blocked clauses.\n", m->qbce_eliminated_clauses);
    //    V1("QBCE detected %zu irrelevant variables.\n", m->qbce_eliminated_vars);
    //    float var_ratio = 1 - ((float) vector_count(new->vars) / ((float) vector_count(m->vars)));
    //    V3("Ratio of fixed variables %.3f\n", var_ratio);
    //    float clause_ratio = 1 - ((float) new->clause_num / ((float) m->clause_num));
    //    V3("Ratio of fixed clauses %.3f\n", clause_ratio);
    
    CADET* cadet = cadet_init_no_matrix(options);
    
    cadet_init_matrix(cadet, m);
    
    while (true) {
        if (cadet_run(cadet) != CADET_RESULT_UNKNOWN) {
            break;
        }
    }
    
    cadet_print_statistics(cadet);
    
    switch (cadet->result) {
        case CADET_RESULT_UNKNOWN:
            if (! options->print_qdimacs) {
                V0("UNKNOWN\n");
            }
            break;
        case CADET_RESULT_SAT:
            V0("SAT\n");
            
            if (options->certify_SAT) {
                aiger* certificate = qbf_Skolem_certificate(cadet->matrix, options);
                
                V0("Certificate has %u gates.\n", certificate->num_ands);
                FILE* certificate_file = fopen(options->certificate_file_name, "w");
                if (!certificate_file) {
                    V0("Error: Cannot open file \"%s\" to write to.\n", options->certificate_file_name);
                } else {
                    V0("Writing certificate to file \"%s\".\n", options->certificate_file_name);
                    aiger_write_to_file(certificate, options->certificate_aiger_mode, certificate_file);
                }
                free(certificate); // TODO: cannot free the aiger-internal objects?!
            }
            
            break;
        case CADET_RESULT_UNSAT:
            V0("UNSAT\n");
            break;
    }
    
    return cadet->result;
}

CADET* cadet_init() {
    CADET* cadet = cadet_init_no_matrix(default_options());
    cadet->matrix = matrix_init();
    return cadet;
}

cadet_res cadet_solve(CADET* cadet) {
    if (cadet->state == CADET_CONFLICT) {
        return CADET_RESULT_UNSAT;
    }
    assert(cadet->state == CADET_READY);
    
    cadet->next_restart = cadet->initial_restart;
    cadet->conflicts = 0;
    
    satsolver_push(cadet->skolem);
    
    while (true) {
        if (cadet_run(cadet) != CADET_RESULT_UNKNOWN) {
            break;
        }
    }
    
    satsolver_pop(cadet->skolem);
    
    return cadet->result;
}

void cadet_free(CADET* cadet) {
    matrix_free(cadet->matrix);
    map_free(cadet->learnt_clauses_propagation_check_after_backtracking);
    map_free(cadet->variables_contained_in_conflict_analysis_heap);
    heap_free(cadet->variables_to_check_for_conflict_analysis);
    statistics_free(cadet->propagation_conflict_timer);
    statistics_free(cadet->decision_conflict_timer);
    vector_free(cadet->skolem_vars);
    satsolver_free(cadet->skolem);
    
    free(cadet);
}

// Adds a new innermost universal quantifier.
void cadet_new_universal_quantifier(CADET* cadet) {
    assert(cadet->state == CADET_READY);
    matrix_new_scope(cadet->matrix, QUANTIFIER_UNIVERSAL);
}

// Adds a new innermost existential quantifier.
void cadet_new_existential_quantifier(CADET* cadet) {
    assert(cadet->state == CADET_READY);
    matrix_new_scope(cadet->matrix, QUANTIFIER_EXISTENTIAL);
}

// Adds a new variable with given ID to the innermost quantifier.
void cadet_create_var(CADET* cadet, int var_id) {
    assert(cadet->state == CADET_READY);
    assert(var_id > 0);
    assert(! map_contains(cadet->matrix->var_lookup, var_id));
    MVar* v = matrix_add_variable_to_last_scope(cadet->matrix, var_id);
    if (v->scope->qtype == QUANTIFIER_UNIVERSAL) {
        vector_add(cadet->skolem_vars, v);
    }
    if (satsolver_get_max_var(cadet->skolem) < cadet->matrix->max_var_id) {
        satsolver_set_max_var(cadet->skolem, cadet->matrix->max_var_id);
    }
}

// Adds a new literal to the current clause. The literal 0 closes the
// current clause and adds it to the matrix. Unclosed clauses are ignored
// during solving.
void cadet_add_lit(CADET* cadet, int lit) {
    assert(lit == 0 || cadet_variable_exists(cadet, abs(lit)));
    if (cadet->state == CADET_CONFLICT) {
        return;
    }
    assert(cadet->state == CADET_READY);
    MClause* c = NULL;
    if (cadet->matrix->push_count == 0) {
        c = matrix_add_lit(cadet->matrix, lit);
    } else {
        c =  matrix_add_lit_undoable(cadet->matrix, lit);
    }
    
    if (c != NULL) {
        c->original = 1;
        if (c->size == 0) {
            cadet->state = CADET_CONFLICT;
            cadet->result = CADET_RESULT_UNSAT;
            cadet->refuting_assignment = int_vector_init();
        } else {
            check_for_unique_consequence(cadet, c);
        }
    }
}

void cadet_cancel_current_clause(CADET* cadet) {
    int_vector_free(cadet->matrix->new_clause);
    cadet->matrix->new_clause = int_vector_init();
}

bool cadet_variable_exists(CADET* cadet, int var) {
    return map_contains(cadet->matrix->var_lookup, var);
}

int_vector* cadet_refuting_assignment(CADET* cadet) {
    assert(cadet->state == CADET_CONFLICT);
    return cadet->refuting_assignment;
}

MVar* cadet_fresh_var(CADET* cadet) {
    assert(cadet->state != CADET_CONFLICT);
    MVar* v = matrix_inc_max_var(cadet->matrix);
    satsolver_inc_max_var(cadet->skolem);
    if (v->scope->qtype == QUANTIFIER_UNIVERSAL) {
        vector_add(cadet->skolem_vars, v);
    }
    if (satsolver_get_max_var(cadet->skolem) < cadet->matrix->max_var_id) {
        satsolver_set_max_var(cadet->skolem, cadet->matrix->max_var_id);
    }
    return v;
}

int cadet_push(CADET* cadet) {
    //    assert(cadet->state == CADET_READY);
    matrix_push_milestone(cadet->matrix);
    return cadet->matrix->push_count;
}

void cadet_recover_from_conflict(CADET* cadet) {
    assert(cadet->state == CADET_CONFLICT);
    assert(cadet->result == CADET_RESULT_UNSAT);
    cadet->matrix->conflicted_clause = NULL;
    int_vector_free(cadet->refuting_assignment);
    cadet->refuting_assignment = NULL;
    while (cadet->matrix->decision_level > 1) {
        assert(cadet->matrix->push_count >= cadet->matrix->decision_level - 1);
        matrix_pop_milestone(cadet->matrix);
        satsolver_pop(cadet->skolem);
        //        cadet->matrix->decision_level -= 1;
    }
    assert(cadet->matrix->decision_level == 1);
    
    cadet->state = CADET_READY;
    cadet->result = CADET_RESULT_UNKNOWN;
}

int cadet_pop(CADET* cadet) {
    assert(cadet->matrix->push_count > 0);
    
    // make sure the solver is in the correct state
    if (cadet->state == CADET_CONFLICT) {
        cadet_recover_from_conflict(cadet);
    }
    
    // now pop the frame
    assert(cadet->matrix->push_count > 0);
    matrix_pop_milestone(cadet->matrix);
    
    // delete learnt clauses; do that more efficiently next time!
    //    abort(); // forgot to unassign dependence levels and decicion levels?? should be handled by undo chain
    MClause* next = NULL;
    for (MClause* c = cadet->matrix->first_clause; c != NULL; c = next) {
        next = c->next;
        assert(next); // Terminate only via the break command. There must be some original clauses somewhere, otherwise nothing could be learnt.
        assert(! c->prev);
        if (! c->original) { // c->learnt ?
            matrix_remove_clause(cadet->matrix, c);
        } else {
            assert(c->original);
            break; // using that learnt clauses are only added to the beginning of the clause list.
        }
    }
    
    return cadet->matrix->push_count;
}


