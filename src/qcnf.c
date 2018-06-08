//
//  qcnf.c
//  cadet
//
//  Created by Markus Rabe on 14/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "qcnf.h"

#include "log.h"
#include "util.h"
#include "heap.h"
#include "c2_rl.h"

#include <string.h>
#include <assert.h>
#include <stdint.h>

bool qcnf_contains_clause_with_only_universals(QCNF* qcnf) {
    return int_vector_count(qcnf->universal_clauses) > 0;
}
bool qcnf_is_trivially_true(QCNF* qcnf) {
    return vector_count(qcnf->active_clauses) == 0;
}

bool qcnf_is_propositional(QCNF* qcnf) {
    return qcnf->problem_type == QCNF_PROPOSITIONAL;
}
bool qcnf_is_2QBF(QCNF* qcnf) {
    return qcnf->problem_type == QCNF_2QBF;
}
bool qcnf_is_DQBF(QCNF* qcnf) {
    return qcnf->problem_type == QCNF_DQBF;
}

bool qcnf_var_has_unique_maximal_dependency(QCNF* qcnf, unsigned var_id) {
    Var* v = var_vector_get(qcnf->vars, var_id);
    return !qcnf_is_DQBF(qcnf) && v->scope_id == (vector_count(qcnf->scopes) - 1);
}

// Clauses
bool qcnf_contains_literal(Clause* clause, Lit lit) {
    assert(lit != 0);
    for (int i = 0; i < clause->size; i++) {
        if (clause->occs[i] == lit) {
            return true;
        }
    }
    return false;
}

int qcnf_contains_variable(Clause* clause, Var* var) { // 0 if not contained, otherwise return lit.
    for (int i = 0; i < clause->size; i++) {
        if ((unsigned) abs(clause->occs[i]) == var->var_id) {
            return clause->occs[i];
        }
    }
    return 0;
}

bool qcnf_check_if_clause_is_universal(QCNF* qcnf, Clause* c) {
    c->universal_clause = true;
    for (unsigned i = 0; i < c->size; i++) {
        c->universal_clause = c->universal_clause && qcnf_is_universal(qcnf, lit_to_var(c->occs[i]));
    }
    return c->universal_clause;
}

bool qcnf_is_learnt_clause(Clause* c) {
    return !c->original && c->consistent_with_originals;
}

bool qcnf_is_learnt_clause_idx(QCNF* qcnf, unsigned clause_idx) {
    Clause* c = vector_get(qcnf->all_clauses, clause_idx);
    return qcnf_is_learnt_clause(c);
}

bool qcnf_is_original_clause(QCNF* qcnf, unsigned clause_idx) {
    Clause* c = vector_get(qcnf->all_clauses, clause_idx);
    return c->original;
}
bool qcnf_is_active(QCNF* qcnf, unsigned clause_idx) {
    Clause* c = vector_get(qcnf->all_clauses, clause_idx);
    return c->active;
}

bool qcnf_is_duplicate(QCNF* qcnf, Clause* c) {
    if (c->size == 0) { // check if there is already an empty clause
        for (unsigned i = 0; i < int_vector_count(qcnf->universal_clauses); i++) {
            Clause* other = vector_get(qcnf->all_clauses,
                                       (unsigned) int_vector_get(qcnf->universal_clauses, i));
            if (other != c && other->size == 0) {
                return true;
            }
        }
        return false;
    }
    Lit first = c->occs[0];
    Var* v = var_vector_get(qcnf->vars, lit_to_var(first));
    vector* occs = first > 0 ? &v->pos_occs : &v->neg_occs;
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* other = vector_get(occs, i);
        if (c != other && c->size == other->size) {
            bool all_equal = true;
            for (unsigned j = 0; j < c->size; j++) {
                all_equal = all_equal && (c->occs[j] == other->occs[j]);
            }
            if (all_equal) {
                V2("Warning: clause %u is duplicate of %d.\n", c->clause_idx, other->clause_idx);
                if (debug_verbosity >= 3) {
                    qcnf_print_clause(c, stdout);
                }
                return true;
            }
        }
    }
    return false;
}


// VARIABLES

bool qcnf_is_existential(QCNF* qcnf, unsigned var_id) {
    Var* v = var_vector_get(qcnf->vars, var_id);
    return ! v->is_universal;
}
bool qcnf_is_universal(QCNF* qcnf, unsigned var_id) {
    Var* v = var_vector_get(qcnf->vars, var_id);
    return v->is_universal;
}
bool qcnf_is_original(QCNF* qcnf, unsigned var_id) {
    Var* v = var_vector_get(qcnf->vars, var_id);
    return v->original;
}

vector* qcnf_get_occs_of_lit(QCNF* qcnf, Lit lit) {
    assert(lit != 0);
    Var* v = var_vector_get(qcnf->vars, lit_to_var(lit));
    return lit > 0 ? &v->pos_occs : &v->neg_occs;
}

// DOMAINS

unsigned qcnf_scope_init(QCNF* qcnf, int_vector* vars) {
    assert(int_vector_is_strictly_sorted(vars));
    
    Scope* scope = malloc(sizeof(Scope));
    scope->vars = vars;
    vector_add(qcnf->scopes, scope);
    unsigned scope_id = vector_count(qcnf->scopes) - 1;
    return scope_id;
}

unsigned qcnf_scope_init_as_intersection(QCNF* qcnf, Scope* d1, Scope* d2) {
    assert(qcnf_is_DQBF(qcnf));
    int_vector* vars = int_vector_init();
    int_vector* vars_smaller = int_vector_count(d1->vars) <  int_vector_count(d2->vars) ? d1->vars : d2->vars;
    int_vector* vars_larger  = int_vector_count(d1->vars) >= int_vector_count(d2->vars) ? d1->vars : d2->vars;
    for (unsigned i = 0; i < int_vector_count(vars_smaller); i++) {
        int var_id = int_vector_get(vars_smaller, i);
        if (int_vector_find_sorted(vars_larger, var_id)) {
            int_vector_add(vars, var_id);
        }
    }
    
    return qcnf_scope_init(qcnf, vars);
}

void qcnf_scope_free(Scope* d) {
    int_vector_free(d->vars);
    free(d);
}

unsigned qcnf_get_empty_scope(QCNF* qcnf) {
#ifdef DEBUG
    if (qcnf_is_DQBF(qcnf)) {
        Scope* d = vector_get(qcnf->scopes, 0);
        assert(int_vector_count(d->vars) == 0);
    }
#endif
    return 0;
}


// COMPARATORS

int qcnf_compare_clauses_by_size (const void * a, const void * b) {
    Clause* c1 = (Clause*) a;
    Clause* c2 = (Clause*) b;
    return ((int) c1->size) - ((int)c2->size);
}

int qcnf_compare_variables_by_occ_num (const void * a, const void * b) {
    Var* v1 = (Var*) a;
    Var* v2 = (Var*) b;
    return ((int)vector_count(&v1->pos_occs) + (int)vector_count(&v1->neg_occs)) - ((int)vector_count(&v2->pos_occs) + (int)vector_count(&v2->neg_occs));
}

int qcnf_compare_literal_pointers_by_var_id(const void * a, const void * b) {
    int x = abs( *(int*) a );
    int y = abs( *(int*) b );
    return ( x - y );
}
int qcnf_compare_literals_by_var_id(const void * a, const void * b) {
    return ( abs((int)a) - abs((int)b) );
}

QCNF* static_qcnf_variable_for_sorting = NULL; // TODO: this prevents C2 from being concurrent

int qcnf_compare_scope_ids(QCNF* qcnf, unsigned scope_id1, unsigned scope_id2) {
    if (!qcnf_is_DQBF(qcnf)) {
        return (int) scope_id1 - (int) scope_id2;
    }
    Scope* d1 = vector_get(qcnf->scopes, scope_id1);
    Scope* d2 = vector_get(qcnf->scopes, scope_id2);
    return (int) int_vector_count(d1->vars) - (int) int_vector_count(d2->vars);
}

// universals < existentials, then scope size, then var_id
int qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id(QCNF* qcnf, const void * a, const void * b) {
    Lit l1 = *(Lit*) a;
    Lit l2 = *(Lit*) b;
    Var* v1 = var_vector_get(qcnf->vars, lit_to_var(l1));
    Var* v2 = var_vector_get(qcnf->vars, lit_to_var(l2));
    int level_diff =  (int) v2->is_universal - (int) v1->is_universal;
    if (level_diff != 0) {
        return level_diff;
    }
    if (! v1->is_universal && ! v2->is_universal) {
        int scope_cmp = qcnf_compare_scope_ids(qcnf, v1->scope_id,v2->scope_id);
        if (scope_cmp != 0) {
            return scope_cmp;
        }
    }
    return (int)v1->var_id - (int)v2->var_id;
}
// this version does not need qcnf as an argument but uses the (hacky) static variable "static_qcnf_variable_for_sorting"
int qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id__static_qcnf(const void * a, const void * b) {
    return qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id(static_qcnf_variable_for_sorting, a, b);
}

QCNF* qcnf_init() {
    QCNF* qcnf = malloc(sizeof(QCNF));
    
    qcnf->active_clauses = vector_init();
    qcnf->all_clauses = vector_init();
    qcnf->clause_iterator_token = 0;
    
    qcnf->vars = var_vector_init();
    Var nullvar;
    memset(&nullvar, 0, sizeof(Var));
    var_vector_add(qcnf->vars, nullvar); // Variable with var_id 0 cannot exist
    
    qcnf->scopes = vector_init();
    vector_add(qcnf->scopes, NULL); // this makes sure that after conversion to DQBF, the first scope is still reserved for constants
    qcnf->problem_type = QCNF_PROPOSITIONAL;
    
    qcnf->new_clause = int_vector_init();
    qcnf->universal_clauses = int_vector_init();
    
    qcnf->stack = stack_init(qcnf_undo_op);
    
    qcnf->variable_names = vector_init();
    
    // Statistics
    qcnf->universal_reductions = 0;
    qcnf->deleted_clauses = 0;
    qcnf->blocked_clauses = 0;
    
    return qcnf;
}

QCNF* qcnf_copy(QCNF* other) {
    QCNF* this = qcnf_init();
    for (unsigned i = 0; i < var_vector_count(other->vars); i++) {
        if (qcnf_var_exists(other, i)) {
            Var* v = var_vector_get(other->vars, i);
            qcnf_new_var(this, v->is_universal, v->scope_id, v->var_id);
        }
    }
    Clause_Iterator ci = qcnf_get_clause_iterator(other); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        for (unsigned j = 0; j < c->size; j++) {
            qcnf_add_lit(this, c->occs[j]);
        }
        qcnf_close_clause(this);
    }
    assert(int_vector_count(this->universal_clauses) == int_vector_count(other->universal_clauses));
    return this;
}

Var* qcnf_new_var(QCNF* qcnf, bool is_universal, unsigned scope_id, unsigned var_id) {
    abortif(scope_id >= UINT16_MAX, "Only supports %u scopes, was given %u", UINT16_MAX, scope_id);
    abortif(var_id == 0, "Variables must be greater than 0");
    abortif(qcnf_var_exists(qcnf, var_id), "Tried to create variable %u, but variable with this ID exists already.", var_id);
    abortif(scope_id > INT16_MAX, "Too many quantifiers, only %d quantifier levels supported.", INT16_MAX);
    abortif(scope_id == 0 && is_universal, "Variables in scope 0 cannot be universal. Scope 0 is reserved for constants.");
    if (scope_id > 10000) {
        LOG_WARNING("Huge scope ID detected (>10000).");
    }
    if (var_id > 1000000) {
        LOG_WARNING("Extremely large variable numbers detected (>1000000), consider compactifying variable names.\n");
    }
    abortif(qcnf_is_DQBF(qcnf) && scope_id >= vector_count(qcnf->scopes), "Scope IDs must be initialized before usage for DQBF.");
    
    V4("Introducing new variable %u to qlvl %u, universal: %d\n", var_id, scope_id, is_universal);
    
    while (scope_id >= vector_count(qcnf->scopes)) {
        qcnf_scope_init(qcnf, int_vector_init());
    }
    if (is_universal) {
        Scope* scope = vector_get(qcnf->scopes, scope_id);
        int_vector_add(scope->vars, (int) var_id);
    }
    
    // update the qcnf state // TODO: this is undoable!
    switch (qcnf->problem_type) {
        case QCNF_PROPOSITIONAL:
            if (var_vector_count(qcnf->vars) == 1 && scope_id == 1) { // var_vector_count(qcnf->var) == 1 because the first element is always assigned NULL, see qcnf_init
                qcnf->problem_type = QCNF_2QBF;
            } else if (scope_id != 0) {
                qcnf->problem_type = QCNF_QBF;
            }
            break;
        case QCNF_2QBF:
            if (scope_id != 1) {
                qcnf->problem_type = QCNF_QBF;
            }
            break;
        // nothing to do for QBF and DQBF
        default:
            break;
    }
    
    // create the variable and make sure that all variables with smaller var_ids exist
    while (var_vector_count(qcnf->vars) <= var_id) {
        var_vector_add(qcnf->vars, *var_vector_get(qcnf->vars, 0));
    }
    
    // initialize the variable
    Var* var = var_vector_get(qcnf->vars, var_id);
    assert(var->var_id == 0);
    var->var_id = var_id;
    var->original = true;
    var->scope_id = (unsigned short) scope_id;
    var->is_universal = is_universal;
    vector_init_struct(&var->pos_occs);
    vector_init_struct(&var->neg_occs);
    
    stack_push_op(qcnf->stack, QCNF_OP_NEW_VAR, (void*) (size_t) var->var_id);
    
    return var;
}

bool qcnf_var_exists(QCNF* qcnf, unsigned var_id) {
    return var_id < var_vector_count(qcnf->vars) && var_vector_get(qcnf->vars, var_id)->var_id != 0;
}

void qcnf_universal_reduction(QCNF* qcnf, Clause* clause) {
    if (!qcnf_is_DQBF(qcnf)) {
        unsigned max_scope = 0;
        for (unsigned i = 0; i < clause->size; i++) {
            Lit lit = clause->occs[i];
            Var* v = var_vector_get(qcnf->vars, lit_to_var(lit));
            if (! v->is_universal && v->scope_id > max_scope) {
                max_scope = v->scope_id;
            }
        }
        for (unsigned i = 0; i < clause->size; i++) {
            Lit lit = clause->occs[i];
            Var* v = var_vector_get(qcnf->vars, lit_to_var(lit));
            if (v->is_universal && v->scope_id > max_scope) {
                qcnf->universal_reductions += 1;
                // delete lit from this clause
                for (unsigned j = i; j + 1 < clause->size; j++) {
                    clause->occs[j] = clause->occs[j+1];
                }
                clause->size -= 1;
                i -= 1;
            }
        }
    } else {
        // delete universals that are in nobody's dependency set
        for (unsigned i = 0; i < clause->size; i++) { // delete trailing universal variables
            Lit lit = clause->occs[i];
            Var* v = var_vector_get(qcnf->vars, lit_to_var(lit));
            if (v->is_universal) {
                bool found_v_in_dependency_sets = false;
                for (int j = clause->size - 1; j >= 0; j--) { // delete trailing universal variables
                    Lit existential_lit = clause->occs[j];
                    Var* existential_v = var_vector_get(qcnf->vars, lit_to_var(existential_lit));
                    if ( ! existential_v->is_universal) {
                        Scope* d = vector_get(qcnf->scopes, existential_v->scope_id);
                        if (int_vector_contains_sorted(d->vars, (int) v->var_id)) {
                            found_v_in_dependency_sets = true;
                            break;
                        }
                    } else {
                        break;
                    }
                }
                if (! found_v_in_dependency_sets) {
                    V4("Universal reduction: literal %d is in nobody's dependency set.\n",v->var_id);
                    for (unsigned k = i; k + 1 < clause->size; k++) {
                        clause->occs[k] = clause->occs[k+1];
                    }
                    clause->size--;
                    i--;
                }
            } else {
                break;
            }
        }
    }
}

Clause* qcnf_new_clause(QCNF* qcnf, int_vector* literals) {
    assert(literals == qcnf->new_clause || int_vector_count(qcnf->new_clause) == 0);
    abortif(int_vector_count(literals) > 33554431, "Clause length is greater than 2^25. You're doing it wrong.");
    
    int_vector_sort(literals, qcnf_compare_literal_pointers_by_var_id);
    for (unsigned i = 0; i+1 < int_vector_count(literals); i++) {
        // find pairs of positive/negative literals of the same variable
        if (int_vector_get(literals, i) == int_vector_get(literals, i+1)) {
            int_vector_remove_index(literals, i+1);
            i--;
        } else if (abs(int_vector_get(literals, i)) == abs(int_vector_get(literals, i+1))) {
            return NULL;
        }
    }
    
    assert(sizeof(Clause) == 3 * sizeof(Lit));
    assert( sizeof(Clause) + (size_t) ( (int) sizeof(Lit) * ((int) int_vector_count(literals) - 1) ) == sizeof(int) * (int_vector_count(literals) + 2) );
    size_t bytes_to_allocate_for_literals = sizeof(Lit) * (size_t) ((int) int_vector_count(literals) - 1);
    
    Clause* c = malloc( sizeof(Clause) + bytes_to_allocate_for_literals );
    vector_add(qcnf->all_clauses, c);
    c->clause_idx = vector_count(qcnf->all_clauses) - 1;
    c->original = true;
    c->consistent_with_originals = true;
    c->blocked = false;
    c->universal_clause = true;
    c->is_cube = false;
    c->minimized = false;
    c->active = false;
    c->in_active_clause_vector = false;
    c->size = int_vector_count(literals);
    
    for (unsigned i = 0; i < c->size; i++) {
        int lit = int_vector_get(literals, i);
        assert(lit != 0);
        c->occs[i] = lit;
        unsigned var_id = lit_to_var(lit);
        
        if (! qcnf_var_exists(qcnf,var_id)) {
            LOG_WARNING("Variable %d is not bound. This may be a 3QBF.", var_id);
            qcnf_new_var(qcnf, false, qcnf_get_empty_scope(qcnf), var_id);
        }
        V4("clause %u, lit is %d\n", c->clause_idx, lit);
    }
    
    // Sort literals in variable ... sorry for the awkward use of global variables to simulate partial function evaluation
    abortif(static_qcnf_variable_for_sorting != NULL, "Memory curruption or concurrent usage of static variable static_qcnf_variable_for_sorting.");
    static_qcnf_variable_for_sorting = qcnf; // sorry for this hack; need to reference qcnf from within the sorting procedure
    qsort(c->occs,
          c->size,
          sizeof(int),
          qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id__static_qcnf);
    static_qcnf_variable_for_sorting = NULL;
    
    if (!qcnf_register_clause(qcnf, c)) {
        c = NULL;
    }
    
    if (c && debug_verbosity >= VERBOSITY_ALL) {
        V4("New clause: ");
        qcnf_print_clause(c, stdout);
    }
    
    return c;
}

unsigned qcnf_fresh_universal(QCNF* qcnf) {
    Var* v = qcnf_new_var(qcnf, true, 1, var_vector_count(qcnf->vars));
    return v->var_id;
}

void qcnf_add_lit(QCNF* qcnf, int lit) {
    assert(lit != 0);
    int_vector_add(qcnf->new_clause, lit);
}

Clause* qcnf_close_clause(QCNF* qcnf) {
    Clause* c = qcnf_new_clause(qcnf, qcnf->new_clause);
    int_vector_reset(qcnf->new_clause);
    return c;
}

void qcnf_free_clause(Clause* c) {
    free(c);
}


bool qcnf_register_clause(QCNF* qcnf, Clause* c) {
    if (qcnf_is_duplicate(qcnf,c)) {
        return false;
    }
    
    // Update the occurrence lists
    for (int i = 0; i < c->size; i++) {
        vector_add(qcnf_get_occs_of_lit(qcnf, c->occs[i]), c);
    }
    assert(!c->active);
    c->active = 1;
    if (!c->in_active_clause_vector) {
        c->in_active_clause_vector = 1;
        vector_add(qcnf->active_clauses, c);
    }
    
    qcnf_check_if_clause_is_universal(qcnf, c);
    if (c->universal_clause) {
        V1("CNF contains a universal clause (clause id %u).\n", c->clause_idx);
        int_vector_add(qcnf->universal_clauses, (int) c->clause_idx);
    }
    
    stack_push_op(qcnf->stack, QCNF_OP_NEW_CLAUSE, c);
    return true;
}

void qcnf_unregister_clause(QCNF* qcnf, Clause* c) {
    assert(c->active);
    assert(c->in_active_clause_vector);
    if (c->universal_clause) {
        int_vector_remove(qcnf->universal_clauses, (int) c->clause_idx);
    }
    // Update the occurrence lists
    for (int i = 0; i < c->size; i++) {
        vector* occs = qcnf_get_occs_of_lit(qcnf, c->occs[i]);
        vector_remove_unsorted(occs, c);
    }
    c->active = 0; // will be cleaned up by the clause iterators
    c2_rl_delete_clause(c);
}

void qcnf_delete_clause(QCNF* qcnf, Clause* c) {
    abortif(true, "Don't delete clauses for now.");
    assert(c);
    assert(!c->active);
    assert(!c->in_active_clause_vector);
    qcnf->deleted_clauses += 1;
    qcnf_free_clause(c);
}

void qcnf_free_var(Var* v) {
    assert(v);
    free(v->pos_occs.data);
    free(v->neg_occs.data);
    free(v);
}

void qcnf_free(QCNF* qcnf) {
    for (unsigned i = 0; i < vector_count(qcnf->all_clauses); i++) {
        Clause* c = vector_get(qcnf->all_clauses, i);
        qcnf_free_clause(c);
    }
    vector_free(qcnf->all_clauses);
    vector_free(qcnf->active_clauses);
    stack_free(qcnf->stack);
    var_vector_free(qcnf->vars); // also deallocates the variables
    
    for (unsigned i = 0 ; i < vector_count(qcnf->scopes); i++) {
        Scope* d = vector_get(qcnf->scopes, i);
        if (d) {qcnf_scope_free(d);}
    }
    vector_free(qcnf->scopes);
    for (unsigned i = 0; i < vector_count(qcnf->variable_names); i++) {
        char* str = vector_get(qcnf->variable_names, i);
        free(str);
    }
    vector_free(qcnf->variable_names);
    free(qcnf);
}

void qcnf_push(QCNF* qcnf) {
    stack_push(qcnf->stack);
}

void qcnf_undo_op(void* parent, char type, void* obj) {
//void qcnf_undo_operation(QCNF* m, Operation* op) {
    QCNF* qcnf = (QCNF*) parent;
    switch (type) {
        case QCNF_OP_NEW_CLAUSE:
            assert(obj != NULL);
            Clause* c = (Clause*) obj;
            qcnf_unregister_clause(qcnf, c);
            if (c->universal_clause) {
                int_vector_remove(qcnf->universal_clauses, (int) c->clause_idx);
            }
            break;
        case QCNF_OP_NEW_VAR:
            assert(obj != NULL);
            unsigned var_id = (unsigned) obj;
            Var* v = var_vector_get(qcnf->vars, var_id);
            
            assert(v->var_id != 0 && v->var_id < var_vector_count(qcnf->vars));
            assert(vector_count(&v->pos_occs) == 0);
            assert(vector_count(&v->neg_occs) == 0);
            
            // make sure the variable "doesn't exist" any more
            var_vector_set(qcnf->vars, v->var_id, *var_vector_get(qcnf->vars, 0));
            
            // Clean up the variable vector. In particular this reduces the var_ids for future calls to qcnf_fresh_var:
            Var* nullvar = var_vector_get(qcnf->vars, 0);
            assert(nullvar->var_id == 0);
            while (var_vector_count(qcnf->vars) > 0) {
                Var* last_var = var_vector_get(qcnf->vars, var_vector_count(qcnf->vars) - 1);
                if (last_var->var_id == 0) {
                    var_vector_remove_last_element(qcnf->vars);
                } else {
                    break;
                }
            }
            break;
        
        default:
            V0("Unknown undo operation in qcnf.c.\n");
            NOT_IMPLEMENTED();
    }
}

void qcnf_pop(QCNF* qcnf) {
    stack_pop(qcnf->stack, qcnf);
}

void qcnf_convert_to_DQBF(QCNF* qcnf) {
    for (unsigned i = 0; i < vector_count(qcnf->scopes); i++) {
        assert(vector_get(qcnf->scopes, i) == NULL);
        Scope* scope = malloc(sizeof(Scope));
        scope->vars = int_vector_init();
        vector_set(qcnf->scopes, i, scope);
    }
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        Var* v = var_vector_get(qcnf->vars, i);
        if (v->var_id != 0 && v->is_universal) {
            // v can be used in all scopes higher than its scope ID
            for (unsigned j = v->scope_id; j < vector_count(qcnf->scopes); j++) {
                Scope* s = vector_get(qcnf->scopes, j);
                int_vector_add(s->vars, (int) v->var_id);
            }
        }
    }
    for (unsigned i = 0; i < vector_count(qcnf->scopes); i++) {
        Scope* scope = vector_get(qcnf->scopes, i);
        int_vector_sort(scope->vars, compare_integers_natural_order);
    }
}


////////////////////// PRINTING /////////////////////////

void qcnf_print_clause(Clause* c, FILE* f) {
    if (c) {
        for (int i = 0; i < c->size; i++) {
            fprintf(f, "%d ", c->occs[i]);
        }
        fprintf(f, "0\n");
    }
}

void find_variables_for_level(QCNF* qcnf, int_vector* universals, int_vector* existentials, unsigned level) {
    assert(int_vector_count(universals) == 0);
    assert(int_vector_count(existentials) == 0);
    
    for (unsigned j = 0; j < var_vector_count(qcnf->vars); j++) {
        Var* v = var_vector_get(qcnf->vars, j);
        if (v->var_id != 0 && v->scope_id == level) {
            if (v->is_universal) {
                int_vector_add(universals, (int) v->var_id);
            } else {
                int_vector_add(existentials, (int) v->var_id);
            }
        }
    }
}

void qcnf_print_qdimacs_quantifiers(QCNF* qcnf, FILE* f) {
    int_vector* universals_i = int_vector_init();
    int_vector* existentials_i = int_vector_init();
    for (unsigned i = 0; i < vector_count(qcnf->scopes); i++) {
        int_vector_reset(universals_i);
        int_vector_reset(existentials_i);
        find_variables_for_level(qcnf, universals_i, existentials_i, i);
        
        if (i != 0) {
            fprintf(f, "a ");
            for (unsigned j = 0; j < int_vector_count(universals_i); j++) {
                fprintf(f, "%d ", int_vector_get(universals_i, j));
            }
            fprintf(f, "0\n");
        }
        
        if (int_vector_count(existentials_i) != 0) {
            fprintf(f, "e ");
            for (unsigned j = 0; j < int_vector_count(existentials_i); j++) {
                fprintf(f, "%d ", int_vector_get(existentials_i, j));
            }
            fprintf(f, "0\n");
        }
    }
    int_vector_free(universals_i);
    int_vector_free(existentials_i);
//    if (qcnf_is_DQBF(qcnf)) {
//        for (unsigned i = 0; i < vector_count(qcnf->scopes); i++) {
//            Scope* d = vector_get(qcnf->scopes, i);
//            V1("Scope %u is:  ", i);
//            int_vector_print(d->vars);
//        }
//    } else {
//        V1("Detected linear quantification order. Deleting scope objects.\n");
//        unsigned scope_id_offset = 0; // is needed in case the first scope is propositional
//        for (unsigned i = 0; i < vector_count(qcnf->scopes); i++) {
//            for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
//                Var* v = var_vector_get(qcnf->vars, i);
//                if (v) {
//                    V4("%c%d -> %d, ", v->is_universal ? 'u' : 'e', v->var_id, v->scope_id);
//                }
//            }
//            V4("\n");
//        }
//    }
}

void qcnf_print_qdimacs_file(QCNF* qcnf, FILE* f) {
    unsigned max_var_id = var_vector_count(qcnf->vars) - 1;
    assert(var_vector_get(qcnf->vars, max_var_id) != NULL);
    
    // count actual clauses
    unsigned clause_num = 0;
    Clause_Iterator ci = qcnf_get_clause_iterator(qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        clause_num++;
    }
    
    fprintf(f, "p cnf %d %u\n", max_var_id, clause_num);
    
    qcnf_print_qdimacs_quantifiers(qcnf, f);
    
    ci = qcnf_get_clause_iterator(qcnf);
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        qcnf_print_clause(c, f);
    }
}

void qcnf_print_qdimacs(QCNF* qcnf) {
    qcnf_print_qdimacs_file(qcnf, stdout);
}

void qcnf_print_statistics(QCNF* qcnf) {
    unsigned existential_var_count = 0;
    unsigned universal_var_count = 0;
    for (unsigned j = 0; j < var_vector_count(qcnf->vars); j++) {
        Var* v = var_vector_get(qcnf->vars, j);
        if (v->var_id == 0) {
            continue;
        }
        if ( ! v->is_universal) {
            existential_var_count++;
        } else {
            universal_var_count++;
        }
    }
    
    V0("QCNF statistics:\n")
    V0("  Scopes: %u\n", vector_count(qcnf->scopes));
    V0("  Existential variables: %u\n", existential_var_count);
    V0("  Universal variables: %u\n", universal_var_count);
    V0("  Clauses: %u\n", vector_count(qcnf->active_clauses));
    V0("  Universal reductions: %u\n", qcnf->universal_reductions);
    V0("  Deleted clauses: %u\n", qcnf->deleted_clauses);
}

//////////// INVARIANTS ///////////

void qcnf_check_invariants_variable(QCNF* qcnf, Var* v) {
    if (v->var_id != 0) {
        abortif(v->scope_id >= vector_count(qcnf->scopes), "Illegal scope ID of variable %d", v->var_id);
//    vector_check_invariants(&v->pos_occs);
//    vector_check_invariants(&v->neg_occs);
        abortif(v->pos_occs.count > vector_count(qcnf->active_clauses),"");
        abortif(v->neg_occs.count > vector_count(qcnf->active_clauses),"");
        abortif(v->scope_id > 0 || !v->is_universal,"");
        abortif(var_vector_get(qcnf->vars, v->var_id) != v, "Variable not found in var vector.");
    } else {
        abortif(v->scope_id == 0,"");
        abortif(v->original == 0,"");
        abortif(v->is_universal == 0,"");
        abortif(v->pos_occs.count == 0,"");
        abortif(v->neg_occs.count == 0,"");
        abortif(v->pos_occs.data == 0,"");
        abortif(v->neg_occs.data == 0,"");
    }
    
}

void qcnf_check_invariants_clause(QCNF* qcnf, Clause* c) {
    if (!c->active) {
        assert(!vector_contains(qcnf->active_clauses, c));
    } else {
        for (unsigned i = 1; i < c->size; i++) {
            Lit prev = c->occs[i-1];
            Lit cur = c->occs[i];
            assert(qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id(qcnf, &prev, &cur) < 0);
        }
    }
}

void qcnf_check_invariants(QCNF* qcnf) {
    for (unsigned i = 0; i < vector_count(qcnf->all_clauses); i++) {
        Clause* c = vector_get(qcnf->all_clauses, i);
        qcnf_check_invariants_clause(qcnf, c);
    }
    for (unsigned i = 1; i < var_vector_count(qcnf->vars); i++) {
        Var* v = var_vector_get(qcnf->vars, i++);
        if (v && v->var_id == i) {
            qcnf_check_invariants_variable(qcnf, v);
        }
        
    }
}

unsigned qcnf_get_scope(QCNF* qcnf, unsigned var_id) {
    assert(var_id != 0);
    Var* v = var_vector_get(qcnf->vars, var_id);
    assert(v->var_id == var_id);
    return v->scope_id;
}

bool qcnf_is_resolvent_tautological(QCNF* qcnf, Clause* c1, Clause* c2, unsigned var_id) {
    assert(qcnf_contains_literal(c1, (Lit) var_id) && qcnf_contains_literal(c2, - (Lit) var_id) || (qcnf_contains_literal(c2, (Lit) var_id) || qcnf_contains_literal(c1, - (Lit) var_id)));
    assert(!qcnf_is_DQBF(qcnf)); // otherwise scope comparison below breaks
    unsigned this_scope = qcnf_get_scope(qcnf, var_id);
    for (unsigned i = 0; i < c1->size; i++) {
        Lit other_lit = c1->occs[i];
        unsigned other_scope = qcnf_get_scope(qcnf, lit_to_var(other_lit));
        if (lit_to_var(other_lit) != var_id && this_scope <= other_scope && qcnf_contains_literal(c2, - other_lit)) {
            return true;
        }
    }
    return false;
}

// TODO: implement version that requires only a single pass
//bool qcnf_is_resolvent_tautological_fast(Clause* c1, Clause* c2, unsigned var_id) {
////    for (unsigned i = 0; c1->size < i; i++) {
////
////    }
//}

/* Check if c1 is a subset of c2, excluding literals of var_id.
 *
 */
bool qcnf_antecedent_subsubsumed(QCNF* qcnf, Clause* c1, Clause* c2, unsigned var_id) {
    unsigned j = 0;
    bool res = true;
    for (unsigned i = 0; i < c1->size; i++) {
        if (lit_to_var(c1->occs[i]) == var_id) {
            continue;
        }
        while(qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id(qcnf, &c1->occs[i], &c2->occs[j]) > 0) {
            j++;
            if (j >= c2->size) {
                res = false;
                goto validate_and_return;
            }
        }
        if (c1->occs[i] != c2->occs[j]) {
            res = false;
            goto validate_and_return;
        }
    }
    
validate_and_return: // check that the result is correct ... this function is too easy to get wrong
#ifdef DEBUG
    assert(true);
    bool alt_res = true;
    for (unsigned i = 0; i < c1->size; i++) {
        if (lit_to_var(c1->occs[i]) != var_id && ! qcnf_contains_literal(c2, c1->occs[i])) {
            alt_res = false;
        }
    }
    assert(alt_res == res);
#endif
    return res;
}

bool qcnf_remove_literal(QCNF* qcnf, Clause* c, Lit l) {
    vector* occs = qcnf_get_occs_of_lit(qcnf, l);
    vector_remove_unsorted(occs, c);
    unsigned i = 0;
    bool found = false;
    for (; i < c->size; i++) {
        if (c->occs[i] == l) {
            break;
        }
    }
    found = i < c->size;
    for (unsigned j = i+1; j < c->size; j++) {
        c->occs[j-1] = c->occs[j];
    }
    if (found) {
        assert(c->size > 0);
        c->size -= 1;
    }
    return found;
}


bool qcnf_occus_only_in_binary_clauses(QCNF* qcnf, Lit lit) {
    vector* occs = qcnf_get_occs_of_lit(qcnf, lit);
    for (unsigned i = 0; i < vector_count(occs); i++) {
        Clause* c = (Clause*) vector_get(occs, i);
        if (c->size != 2) {
            return false;
        }
    }
    return true;
}

Lit qcnf_get_other_lit(Clause* c, Lit lit) {
    assert(c->size == 2); // actually not needed
    assert(qcnf_contains_literal(c, lit));
    for (unsigned i = 0; i < c->size; i++) {
        if (c->occs[i] != lit) {
            return c->occs[i];
        }
    }
    assert(false);
    return 0;
}


// Detects equivalences
bool qcnf_occus_in_xor_halfdef(QCNF* qcnf, Lit this_lit) {
    vector* occs = qcnf_get_occs_of_lit(qcnf, this_lit);
    if (vector_count(occs) != 2) {
        return false;
    }
    Clause* first = vector_get(occs, 0);
    Clause* second = vector_get(occs, 1);
    if (first->size != 3 || second->size != 3) {
        return false;
    }
    assert(qcnf_contains_literal(first,  this_lit));
    assert(qcnf_contains_literal(second, this_lit));
    for (unsigned i = 0; i < first->size; i++) {
        Lit lit = first->occs[i];
        if (lit != this_lit  &&  ! qcnf_contains_literal(second, - lit)) {
            return false;
        }
    }
    return true;
}

Clause* qcnf_close_PG_clause(QCNF* qcnf) {
    Clause* new = qcnf_close_clause(qcnf);
    if (new) {
        // qcnf_print_clause(new, stdout);
        new->original = 0;
        new->consistent_with_originals = 1;
        new->blocked = 1;
    }
    return new;
}

/* Plaisted-Greenbaum is a Tseitin-like encoding that omits some clauses.
 * This function adds the missing clauses without changing the truth of the formula.
 * This may help to improve determinicity propagation.
 */
void qcnf_plaisted_greenbaum_completion(QCNF* qcnf) {
    unsigned added_binary = 0;
    unsigned added_non_binary = 0;
    unsigned added_xor = 0;
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        Var* v = var_vector_get(qcnf->vars, i);
        if (v->var_id != 0 && qcnf_is_existential(qcnf, v->var_id)) {
            
            int only_binary_polarity = 0;
            unsigned add_long_clause_cost = UINT_MAX;
            
            int single_occurrence_polarity = 0;
            unsigned add_binary_clauses_cost = UINT_MAX;
            
            int xor_halfdef_polarity = 0;
            unsigned complete_xor_cost = UINT_MAX;
            
            for (int polarity = -1; polarity < 2; polarity += 2) {
                Lit this = polarity * (Lit) v->var_id;
                
                if (qcnf_occus_only_in_binary_clauses(qcnf, this)) {
                    vector* binary_occs = qcnf_get_occs_of_lit(qcnf, this);
                    unsigned cost = vector_count(binary_occs);
                    if (cost <= add_long_clause_cost) {
                        only_binary_polarity = polarity;
                        add_long_clause_cost = cost;
                    }
                }
                
                vector* occs = qcnf_get_occs_of_lit(qcnf, this);
                if (vector_count(occs) == 1) {
                    Clause* only_occ = vector_get(occs, 0);
                    unsigned cost = only_occ->size;
                    if (cost < add_binary_clauses_cost) {
                        single_occurrence_polarity = polarity;
                        add_binary_clauses_cost = cost;
                    }
                }
                
                if (qcnf_occus_in_xor_halfdef(qcnf, this)) {
                    vector* occs = qcnf_get_occs_of_lit(qcnf, this);
                    unsigned cost = vector_count(occs);
                    if (cost <= complete_xor_cost) {
                        xor_halfdef_polarity = polarity;
                        complete_xor_cost = cost;
                        assert(complete_xor_cost == 2); // just for now
                    }
                }
            }
            
            assert(! only_binary_polarity || add_long_clause_cost < UINT_MAX);
            assert(! single_occurrence_polarity || add_binary_clauses_cost < UINT_MAX);
            assert(! xor_halfdef_polarity || complete_xor_cost < UINT_MAX);
            
            // Detect half-definitions of equivalence/ite/xor gates.
            // Pattern: (l x1 x2) (l -x1 -x2) being the only two clauses for literal
            if (xor_halfdef_polarity != 0) {
                Lit this = xor_halfdef_polarity * (Lit) v->var_id;
                vector* occs = qcnf_get_occs_of_lit(qcnf, this);
                for (unsigned j = 0; j < vector_count(occs); j++) {
                    int countdown_to_flip = (int) j; // flip the j-th occurrence different than 'this'; can become negative
                    Clause* c = vector_get(occs, j);
                    for (unsigned k = 0 ; k < c->size; k++) {
                        if (c->occs[k] != this) {
                            if (countdown_to_flip == 0) {
                                qcnf_add_lit(qcnf, - c->occs[k]);
                            } else {
                                qcnf_add_lit(qcnf,   c->occs[k]);
                            }
                            countdown_to_flip -= 1;
                        }
                    }
                    qcnf_add_lit(qcnf, - this);
                    Clause* new = qcnf_close_PG_clause(qcnf);
                    if (new) {added_xor += 1;}
                }
            } else {
                if (add_long_clause_cost < UINT_MAX && add_long_clause_cost < add_binary_clauses_cost) {
                    assert(only_binary_polarity);
                    Lit this = only_binary_polarity * (Lit) v->var_id;
                    
                    vector* occs = qcnf_get_occs_of_lit(qcnf, this);
                    for (unsigned j = 0; j < vector_count(occs); j++) {
                        Clause* c = vector_get(occs, j);
                        assert(c->size == 2);
                        Lit other = qcnf_get_other_lit(c, this);
                        qcnf_add_lit(qcnf, - other);
                    }
                    qcnf_add_lit(qcnf, -this);
                    if (qcnf_close_PG_clause(qcnf)) {added_non_binary += 1;}
                }
                
                if (add_binary_clauses_cost < UINT_MAX && add_binary_clauses_cost <= add_long_clause_cost) {
                    assert(single_occurrence_polarity);
                    Lit this = single_occurrence_polarity * (Lit) v->var_id;
                    vector* occs = qcnf_get_occs_of_lit(qcnf, this);
                    assert(vector_count(occs) == 1);
                    
                    Clause* c = (Clause*) vector_get(occs, 0);
                    for (unsigned j = 0; j < c->size; j++) {
                        Lit l = c->occs[j];
                        if (lit_to_var(l) != v->var_id) {
                            qcnf_add_lit(qcnf, -l);
                            qcnf_add_lit(qcnf, - this);
                            if (qcnf_close_PG_clause(qcnf)) {added_binary += 1;}
                        }
                    }
                }
            }
            
        }
    }
    V1("Plaisted-Greenbaum completion added %u binary and %u non-binary and %u xor clauses.\n", added_binary, added_non_binary, added_xor);
}

bool qcnf_is_blocked_by_lit(QCNF* qcnf, Clause* c, Lit pivot) {
    assert(qcnf_contains_literal(c, pivot));
    vector* occs = qcnf_get_occs_of_lit(qcnf, - pivot);
    for (unsigned j = 0; j < vector_count(occs); j++) {
        Clause* other = vector_get(occs, j);
        if ( ! qcnf_is_resolvent_tautological(qcnf, c, other, lit_to_var(pivot))) {
            return false;
        }
    }
    return true;
}

bool qcnf_is_blocked(QCNF* qcnf, Clause* c) {
    for (unsigned i = 0; i < c->size; i++) {
        Lit pivot = c->occs[i];
        if (qcnf_is_universal(qcnf, lit_to_var(pivot))) {
            continue;
        }
        if (qcnf_is_blocked_by_lit(qcnf, c, pivot)) {
            return true;
        }
    }
    return false;
}

void qcnf_blocked_clause_detection(QCNF* qcnf) {
    Clause_Iterator ci = qcnf_get_clause_iterator(qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        if (qcnf_is_blocked(qcnf, c)) {
            c->blocked = 1;
            qcnf->blocked_clauses += 1;
            qcnf_unregister_clause(qcnf, c);
            
            V1("Clause deleted: ");
            if(debug_verbosity >= VERBOSITY_LOW) {qcnf_print_clause(c, stdout);}
        }
    }
    V1("Removed %u blocked clauses.\n", qcnf->blocked_clauses);
}
