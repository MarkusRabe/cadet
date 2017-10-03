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

#include <string.h>
#include <assert.h>
#include <stdint.h>

bool qcnf_contains_empty_clause(QCNF* qcnf) {
    return qcnf->empty_clause != NULL;
}
bool qcnf_is_trivially_true(QCNF* qcnf) {
    return vector_count(qcnf->clauses) == 0;
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

bool qcnf_is_duplicate(QCNF* qcnf, Clause* c) {
    if (c->size == 0) {
        return qcnf->empty_clause != NULL;
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

vector* qcnf_get_occs_of_lit(QCNF* qcnf, Lit lit) {
    Var* v = var_vector_get(qcnf->vars, lit_to_var(lit));
    return lit > 0 ? &v->pos_occs : &v->neg_occs;
}

// DOMAINS

unsigned qcnf_scope_init(QCNF* qcnf, int_vector* vars) {
    assert(qcnf_is_DQBF(qcnf));
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
    
    qcnf->clauses = vector_init();
    qcnf->cubes = vector_init();
    qcnf->next_free_clause_id = 0;
    
    qcnf->vars = var_vector_init();
    Var nullvar;
    memset(&nullvar, 0, sizeof(Var));
    var_vector_add(qcnf->vars, nullvar); // Variable with var_id 0 cannot exist
    
    qcnf->scopes = vector_init();
    vector_add(qcnf->scopes, NULL); // this makes sure that after conversion to DQBF, the first scope is still reserved for constants
    qcnf->problem_type = QCNF_PROPOSITIONAL;
    
    qcnf->new_clause = int_vector_init();
    qcnf->empty_clause = NULL;
    
    qcnf->universals_constraints = int_vector_init();
    
    qcnf->stack = stack_init(qcnf_undo_op);
    
    qcnf->universal_reductions = 0;
    qcnf->deleted_clauses = 0;
    
    return qcnf;
}

Var* qcnf_new_var(QCNF* qcnf, bool is_universal, unsigned scope_id, unsigned var_id) {
    abortif(var_id == 0, "Variables must be greater than 0");
    abortif(qcnf_var_exists(qcnf, var_id), "Tried to create variable %u, but variable with this ID exists already.", var_id);
    abortif(scope_id > INT16_MAX, "Too many quantifiers, only %d quantifier levels supported.", INT16_MAX);
    abortif(scope_id == 0 && is_universal, "Variables in scope 0 cannot be universal");
    if (scope_id > 10000) {
        LOG_WARNING("Huge scope ID detected (>10000).");
    }
    if (var_id > 1000000) {
        LOG_WARNING("Extremely large variable numbers detected (>1000000), consider compactifying variable names.\n");
    }
    abortif(qcnf_is_DQBF(qcnf) && scope_id >= vector_count(qcnf->scopes), "Scope IDs must be initialized before usage for DQBF.");
    
    V4("Introducing new variable %u to qlvl %u, universal: %d\n",var_id, scope_id, is_universal);
    
    while (scope_id >= vector_count(qcnf->scopes)) {
        vector_add(qcnf->scopes, NULL);
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
    
    var->c2_vd = c2_initial_var_data();
    
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

unsigned qcnf_get_smallest_free_clause_id(QCNF* qcnf) {
    assert(qcnf->next_free_clause_id <= vector_count(qcnf->clauses));
    assert(vector_count(qcnf->clauses) == qcnf->next_free_clause_id || vector_get(qcnf->clauses, qcnf->next_free_clause_id) == NULL);
    
    unsigned res = qcnf->next_free_clause_id;
    qcnf->next_free_clause_id += 1; 
    while (qcnf->next_free_clause_id < vector_count(qcnf->clauses) && vector_get(qcnf->clauses, qcnf->next_free_clause_id) != NULL) {
        qcnf->next_free_clause_id += 1;
    }
    if (qcnf->next_free_clause_id > vector_count(qcnf->clauses)) {
        vector_add(qcnf->clauses, NULL);
    }
    return res;
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
    
    assert( sizeof(Clause) + (size_t) ( (int) sizeof(Lit) * ((int) int_vector_count(literals) - 1) ) == sizeof(int) * (int_vector_count(literals) + 2) );
    size_t bytes_to_allocate_for_literals = sizeof(Lit) * (size_t) ((int) int_vector_count(literals) - 1);
    
    Clause* c = malloc( sizeof(Clause) + bytes_to_allocate_for_literals );
    c->clause_id = qcnf_get_smallest_free_clause_id(qcnf);
    c->original = true;
    c->consistent_with_originals = true;
    c->PG = false;
    c->size = int_vector_count(literals);
    for (unsigned i = 0; i < c->size; i++) {
        int lit = int_vector_get(literals, i);
        assert(lit != 0);
        
        c->occs[i] = lit;
        unsigned var_id = lit_to_var(lit);
        if (! qcnf_var_exists(qcnf,var_id)) {
            V1("Warning: Variable %d is not bound.\n", var_id);
            qcnf_new_var(qcnf, false, qcnf_get_empty_scope(qcnf), var_id);
        }
    }
    
    abortif(static_qcnf_variable_for_sorting != NULL, "Memory curruption or concurrent usage of static variable static_qcnf_variable_for_sorting.");
    
    static_qcnf_variable_for_sorting = qcnf; // sorry for this hack; need to reference qcnf from within the sorting procedure
    qsort(c->occs, c->size, sizeof(int), qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id__static_qcnf);
    static_qcnf_variable_for_sorting = NULL;
    
    qcnf_universal_reduction(qcnf, c);

    if (qcnf_is_duplicate(qcnf,c)) {
        V3("Warning: detected duplicate clause. ");
        if (debug_verbosity >= 3) {
            qcnf_print_clause(c, stdout);
        }
        free(c);
        return NULL;
    }
    
    qcnf_register_clause(qcnf, c);
    
    if (c->size == 0) {
        stack_push_op(qcnf->stack, QCNF_UPDATE_EMPTY_CLAUSE, qcnf->empty_clause);
        qcnf->empty_clause = c;
    }
    
    if (c != NULL) { // to avoid too many operations in the undo-chain
        stack_push_op(qcnf->stack, QCNF_OP_NEW_CLAUSE, c);
    }
    
    if (debug_verbosity >= VERBOSITY_ALL) {
        V4("New clause %d: ", c->clause_id);
        qcnf_print_clause(c, stdout);
    }
    
    return c;
}

Var* qcnf_fresh_var(QCNF* qcnf, unsigned scope_id) {
    Var* v = qcnf_new_var(qcnf, false, scope_id, var_vector_count(qcnf->vars));
    assert(!v->is_universal);
    return v;
}

void qcnf_add_lit(QCNF* qcnf, int lit) {
    assert(lit != 0);
    int_vector_add(qcnf->new_clause, lit);
}

Clause* qcnf_close_clause(QCNF* qcnf) {
    Clause* c = qcnf_new_clause(qcnf, qcnf->new_clause);
    int_vector_reset(qcnf->new_clause);
    if (c && qcnf->empty_clause == NULL && c->size == 0) {
        qcnf->empty_clause = c;
    }
    return c;
}

void qcnf_free_clause(Clause* c) {
    free(c);
}

void qcnf_free_var(Var* v) {
    assert(v);
    free(v->pos_occs.data);
    free(v->neg_occs.data);
    free(v);
}

void qcnf_free(QCNF* qcnf) {
    for (unsigned i = 0; i < vector_count(qcnf->clauses); i++) {
        qcnf_free_clause(vector_get(qcnf->clauses, i));
    }
    vector_free(qcnf->clauses);
    
    stack_free(qcnf->stack);
    
    var_vector_free(qcnf->vars); // also deallocates the variables
    
    for (unsigned i = 0 ; i < vector_count(qcnf->scopes); i++) {
        Scope* d = vector_get(qcnf->scopes, i);
        if (d) {
            qcnf_scope_free(d);
        }
    }
    vector_free(qcnf->scopes);
    free(qcnf);
}

void qcnf_push(QCNF* qcnf) {
    stack_push(qcnf->stack);
}

void qcnf_remove_clause(QCNF* qcnf, Clause* c) {
    assert(! c->original);
    
    vector_set(qcnf->clauses, c->clause_id, NULL);
    if (c->clause_id < qcnf->next_free_clause_id) {
        qcnf->next_free_clause_id = c->clause_id;
    }
    for (unsigned i = 0; i < c->size; i++) {
        Var* v = var_vector_get(qcnf->vars, lit_to_var(c->occs[i]));
        assert(v->var_id != 0);
        vector* var_occs = c->occs[i] < 0 ? &v->neg_occs : &v->pos_occs;
        bool res = vector_remove_unsorted(var_occs, c);
        assert(res);
    }
    qcnf_free_clause(c);
}


void qcnf_undo_op(void* parent, char type, void* obj) {
//void qcnf_undo_operation(QCNF* m, Operation* op) {
    QCNF* qcnf = (QCNF*) parent;
    switch (type) {
        case QCNF_OP_NEW_CLAUSE:
            assert(obj != NULL);
            Clause* c = (Clause*) obj;
            if (!c->consistent_with_originals) { // protects learned clauses
                qcnf_remove_clause(qcnf, (Clause*) obj);
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
        case QCNF_UPDATE_EMPTY_CLAUSE:
            qcnf->empty_clause = (Clause*) obj;
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
    for (unsigned i = 0; i < vector_count(qcnf->clauses); i++) {
        Clause* c = vector_get(qcnf->clauses, i);
        if (c) {
            clause_num++;
        }
    }
    
    fprintf(f, "p cnf %d %u\n", max_var_id, clause_num);
    
    qcnf_print_qdimacs_quantifiers(qcnf, f);
    
    for (unsigned i = 0; i < vector_count(qcnf->clauses); i++) {
        Clause* c = vector_get(qcnf->clauses, i);
        qcnf_print_clause(c, f);
    }
    return;
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
    V0("  Clauses: %u\n", vector_count(qcnf->clauses));
    V0("  Universal reductions: %u\n", qcnf->universal_reductions);
    V0("  Deleted clauses: %u\n", qcnf->deleted_clauses);
}

//////////// INVARIANTS ///////////

void qcnf_check_invariants_variable(QCNF* qcnf, Var* v) {
    if (v->var_id != 0) {
        abortif(v->scope_id >= vector_count(qcnf->scopes), "Illegal scope ID of variable %d", v->var_id);
//    vector_check_invariants(&v->pos_occs);
//    vector_check_invariants(&v->neg_occs);
        abortif(v->pos_occs.count > vector_count(qcnf->clauses),"");
        abortif(v->neg_occs.count > vector_count(qcnf->clauses),"");
        abortif(v->scope_id > 0 || !v->is_universal,"");
        abortif(v->c2_vd.activity < 0.0, "Activity smaller than 0.");
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
    for (unsigned i = 1; i < c->size; i++) {
        Lit prev = c->occs[i-1];
        Lit cur = c->occs[i];
        assert(qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id(qcnf, &prev, &cur) < 0);
    }
}

void qcnf_check_invariants(QCNF* qcnf) {
    for (unsigned i = 0; i < vector_count(qcnf->clauses); i++) {
        Clause* c = vector_get(qcnf->clauses, i);
        if (c) {
            qcnf_check_invariants_clause(qcnf, c);
        }
    }
    for (unsigned i = 1; i < var_vector_count(qcnf->vars); i++) {
        Var* v = var_vector_get(qcnf->vars, i++);
        if (v && v->var_id == i) {
            qcnf_check_invariants_variable(qcnf, v);
        }
        
    }
}

bool qcnf_is_resolvent_tautological(Clause* c1, Clause* c2, unsigned var_id) {
    assert(qcnf_contains_literal(c1, (Lit) var_id) && qcnf_contains_literal(c2, - (Lit) var_id) || (qcnf_contains_literal(c2, (Lit) var_id) || qcnf_contains_literal(c1, - (Lit) var_id)));
    for (unsigned i = 0; i < c1->size; i++) {
        if (lit_to_var(c1->occs[i]) != var_id && qcnf_contains_literal(c2, - c1->occs[i])) {
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

void qcnf_register_clause(QCNF* qcnf, Clause* c) {
    // Update the occurrence lists
    for (int i = 0; i < c->size; i++) {
        vector_add(qcnf_get_occs_of_lit(qcnf, c->occs[i]), c);
    }
    
    vector_set(qcnf->clauses, c->clause_id, c);
    
    if (c->size == 0) {
        if (qcnf->empty_clause) {
            LOG_WARNING("Found second empty clause. Likely inconsistency.");
        }
        qcnf->empty_clause = c;
    }
}

void qcnf_unregister_clause(QCNF* qcnf, Clause* c) {
    assert(c->size > 0); // otherwise we may also need to keep qcnf->empty_clause consistent
    
    // Update the occurrence lists
    for (int i = 0; i < c->size; i++) {
        vector* occs = qcnf_get_occs_of_lit(qcnf, c->occs[i]);
        vector_remove_unsorted(occs, c);
    }
    
    vector_set(qcnf->clauses, c->clause_id, NULL);
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

void qcnf_delete_clause(QCNF* qcnf, Clause* c) {
    assert(c && ! c->original);
    qcnf->deleted_clauses += 1;
    qcnf_unregister_clause(qcnf, c);
    qcnf_free_clause(c);
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

Lit qcnf_get_other_lit(QCNF* qcnf, Clause* c, Lit lit) {
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

/* Plaisted-Greenbaum is a Tseitin-like encoding that omits some clauses.
 * This function adds the missing clauses without changing the truth of the formula.
 * This may help to improve determinicity propagation.
 */
void qcnf_plaisted_greenbaum_completion(QCNF* qcnf) {
    unsigned added_binary = 0;
    unsigned added_non_binary = 0;
    for (unsigned i = 0; i < var_vector_count(qcnf->vars); i++) {
        Var* v = var_vector_get(qcnf->vars, i);
        if (v->var_id != 0 && ! v->is_universal) {
            
            int only_binary_polarity = 0;
            unsigned add_long_clause_cost = UINT_MAX;
            
            int single_occurrence_polarity = 0;
            unsigned add_binary_clauses_cost = UINT_MAX;
            
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
            }
            
//            if (! only_binary_polarity && ! single_occurrence_polarity) {
//                continue;
//            }
            assert(! only_binary_polarity || add_long_clause_cost < UINT_MAX);
            assert(! single_occurrence_polarity || add_binary_clauses_cost < UINT_MAX);
            
            if (add_long_clause_cost < add_binary_clauses_cost) {
                assert(only_binary_polarity);
                Lit this = only_binary_polarity * (Lit) v->var_id;
                
                vector* occs = qcnf_get_occs_of_lit(qcnf, this);
                for (unsigned j = 0; j < vector_count(occs); j++) {
                    Clause* c = vector_get(occs, j);
                    assert(c->size == 2);
                    Lit other = qcnf_get_other_lit(qcnf, c, this);
                    qcnf_add_lit(qcnf, - other);
                }
                qcnf_add_lit(qcnf, -this);
                Clause* new = qcnf_close_clause(qcnf);
                if (new) {
                    // qcnf_print_clause(new, stdout);
                    added_non_binary += 1;
                    new->original = 0;
                    new->consistent_with_originals = 1;
                    new->PG = 1;
                }
            } else if (add_binary_clauses_cost < add_long_clause_cost) {
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
                        Clause* new = qcnf_close_clause(qcnf);
                        if (new) {
                            // qcnf_print_clause(new, stdout);
                            added_binary += 1;
                            new->original = 0;
                            new->consistent_with_originals = 1;
                            new->PG = 1;
                        }
                    }
                }
            }
            
        }
    }
    V1("Plaisted-Greenbaum completion added %u binary and %u non-binary clauses.\n", added_binary, added_non_binary);
}



