
//
//  matrix.c
//  caqe
//
//  Created by Markus Rabe on 21/11/14.
//  Copyright (c) 2014 Saarland University. All rights reserved.
//

#include <assert.h>
#include <stdint.h>
#include "matrix.h"
#include "log.h"
#include "util.h"

Occ* is_clause_satisfied(MClause* c) {
    for (size_t i = 0; i < c->size; i++) {
        Occ* o = &c->occs[i];
        if (o->var->value == (o->neg ? -1 : 1)) {
            return o;
        }
    }
    return NULL;
}

//bool is_active(Occ* o) { // TODO: inline this check everywhere 
//    assert(o != NULL);
//    return o->var->value == 0;
//}

int matrix_get_lit(Occ* occ) {
    return occ->neg ? -occ->var->var_id : occ->var->var_id;
}

// This reimplements a vector, sorry. The current vector implementation does not like structs as values.
static inline Operation* matrix_new_operation(Matrix* m) {
    if (m->op_count == m->op_size) {
        m->op_size *= 2;
        Operation* newdata = malloc(sizeof(Operation) * m->op_size);
        for (size_t i = 0; i < m->op_count; i++) {
            newdata[i] = m->op_vector[i];
        }
        free(m->op_vector);
        m->op_vector = newdata;
    }
    Operation* op = &m->op_vector[m->op_count];
    m->op_count += 1;
    return op;
}

static inline void matrix_assign_result(Matrix* m, matrix_res res) {
    assert(m->result == MATRIX_UNKNOWN || m->result == res);
    
    Operation* op = matrix_new_operation(m);
    op->type = MATRIX_OP_ASSIGN_MATRIX_RESULT;
    op->previous_result = m->result;
    
    m->result = res;
}

void matrix_propagate_var(Matrix* m, MVar* var, int value) {
    assert(value == -1 || value == 1);
    assert(var->value == 0);
    
    vector* same_value_occs = NULL;
    vector* diff_value_occs = NULL;
    if (value == 1) {
        same_value_occs = var->pos_occs;
        diff_value_occs = var->neg_occs;
    } else {
        same_value_occs = var->neg_occs;
        diff_value_occs = var->pos_occs;
    }
    
    // All those clauses are now satisfied
    for (unsigned i = 0; i < vector_count(same_value_occs); i++) {
        Occ* o = vector_get(same_value_occs, i);
        if (is_clause_satisfied(o->clause)) {
            continue;
        }
        matrix_clause_satisfied(m, o);
    }
    
    // The clauses containing the opposite lit are now more difficult to satisfy
    for (unsigned i = 0; i < vector_count(diff_value_occs); i++) {
        Occ* o = vector_get(diff_value_occs, i);
        if (is_clause_satisfied(o->clause)) {
            continue;
        }
        assert(o->var->scope == var->scope);
        if ( ! o->clause->needs_propagation_check) {
            o->clause->needs_propagation_check = true;
            heap_push(m->clauses_to_check, o->clause);
        }
    }
    
    m->assigned_variables += 1;
    var->value = value;
    V4("Propagating literal %d.\n", var->var_id * var->value);
    
    Operation* op = matrix_new_operation(m);
    op->type = MATRIX_OP_ASSIGN_VAR;
    op->var = var;
}

MScope* matrix_init_scope(Matrix* m, quant qtype) {
    MScope* s = malloc(sizeof(MScope));
    s->level = vector_count(m->scopes);
    s->deactivated = false;
    s->qtype = qtype;
    s->vars = vector_init();
    return s;
}

MScope* matrix_new_scope(Matrix* m, quant qtype) {
    if (matrix_get_last_scope(m)->qtype == qtype) {
        return matrix_get_last_scope(m);
    } else {
        MScope* s = matrix_init_scope(m, qtype);
        vector_add(m->scopes, s);
        return s;
    }
}

int compare_clauses_by_size (const void * a, const void * b) {
    MClause* c1 = (MClause*) a;
    MClause* c2 = (MClause*) b;
    return ((int) c1->size) - ((int)c2->size);
}

int compare_variables_by_occ_num (const void * a, const void * b) {
    MVar* v1 = (MVar*) a;
    MVar* v2 = (MVar*) b;
    return ((int)vector_count(v1->pos_occs) + (int)vector_count(v1->neg_occs)) - ((int)vector_count(v2->pos_occs) + (int)vector_count(v2->neg_occs));
}

Matrix* matrix_init() {
    Matrix* m = malloc(sizeof(Matrix));
    
    m->first_clause = NULL;
    m->clause_num = 0;
    m->max_clause_id = 0;
    m->var_lookup = map_init();
    m->max_var_id = 0;
    
    // Work queues
    m->result = MATRIX_SATISFIABLE;
    m->clauses_to_check = heap_init(compare_clauses_by_size);
    m->variables_to_check = heap_init(compare_variables_by_occ_num);
    m->conflicted_clause = NULL;
    
    m->variables_to_check_for_determinicity = heap_init(compare_variables_by_occ_num);
    
    // Statistics
    m->assigned_variables = 0;
    m->satisfied_clauses = 0;
    m->qbce_eliminated_clauses = 0;
    m->qbce_eliminated_vars = 0;
    m->removed_occurrences_from_occurrence_list = 0;
    
    m->op_size = 1024;
    m->op_vector = malloc(sizeof(Operation) * m->op_size);
    m->op_count = 0;
    
    m->push_count = 0;
    m->decision_level = 1; // 0 represents no decision level
    m->minimal_dependence_lvl = 0;
    
    m->scopes = vector_init();
    vector_add(m->scopes, matrix_init_scope(m, QUANTIFIER_EXISTENTIAL));
    
    m->new_clause = int_vector_init();
    
    m->iteration_number = 0;
    return m;
}

MVar* matrix_new_var(Matrix* m, MScope* scope, int var_id) {
    assert(var_id <= 0);
    MVar* var = malloc(sizeof(MVar));
    
    var->var_id = var_id;
    var->value = 0;
    var->needs_qbce_check = false;
    var->needs_determinicity_check = false;
    var->is_decision_var = false;
    var->is_helper = false;
    var->has_only_blocked_clauses = false;
    
    var->scope = scope;
    
    var->dependence_level = scope->qtype == QUANTIFIER_UNIVERSAL ? scope->level : NO_DEPENDENCE_LVL;
    
    var->pos_occs = vector_init();
    var->neg_occs = vector_init();
    
//    var->pointed_to_in_implication_graph = NULL;
    var->decision_level = NO_DECISION;
    var->activity = 0.0;
    
    m->max_var_id = var_id > m->max_var_id ? var_id : m->max_var_id;
    map_add(m->var_lookup, var_id, var);
    
    return var;
}

MVar* matrix_get_var(Matrix* matrix, int var_id) {
    assert(var_id > 0);
    MVar* var = map_get(matrix->var_lookup, var_id);
    return var;
}

int compare_literals_by_var_id(const void * a, const void * b) {
    return ( abs(*(int*)a) - abs(*(int*)b) );
}

int compare_occurrence_by_level_then_var_id(const void * a, const void * b) {
    Occ* o1 = (Occ*) a;
    Occ* o2 = (Occ*) b;
    int level_diff = (int)o1->var->scope->level - (int)o2->var->scope->level;
    return (level_diff != 0 ? level_diff : abs(o1->var->var_id) - abs(o2->var->var_id) );
}

MClause* matrix_new_clause(Matrix* m, int_vector* literals) {
    int_vector_sort(literals, compare_literals_by_var_id);
    
    for (unsigned i = 0; i+1 < int_vector_count(literals); i++) {
        // find pairs of positive/negative literals of the same variable
        if (int_vector_get(literals, i) == int_vector_get(literals, i+1)) {
            int_vector_remove_index(literals, i+1);
            i--;
        } else if (abs(int_vector_get(literals, i)) == abs(int_vector_get(literals, i+1))) {
            return NULL;
        }
    }
    
//    MClause* c = malloc( sizeof(MClause) + ( sizeof(Occ) * int_vector_count(literals)) );
    MClause* c = malloc(sizeof(MClause));
    
    c->clause_id = -1;
    c->needs_propagation_check = false;
    c->blocked = false;
    c->learnt = false;
    c->original = false;
    c->unconflicting = false;
    
    c->unique_consequence_occ = NULL;
    
//    c->occs = (Occ*) (c + sizeof(MClause));
    c->occs = malloc(sizeof(Occ) * int_vector_count(literals));
    
    c->size = int_vector_count(literals);
    
    for (unsigned i = 0; i < c->size; i++) {
        // occ_init()
        Occ* o = &c->occs[i];
        int lit = (int) int_vector_get(literals, i);
        assert(lit != 0);
        unsigned var_id = lit_to_var(lit);
        MVar* var = NULL;
        if ( ! map_contains(m->var_lookup, (int) var_id)) { // unbound variable, put variable to outermost scope
            MScope* scope = vector_get(m->scopes,0) ;
            int var_name = lit > 0 ? lit : -lit;
            var = matrix_new_var(m, scope, var_name);
            vector_add(scope->vars, var);
        } else {
            var = map_get(m->var_lookup, (int) var_id);
        }
        assert(var != NULL);
        assert(var->var_id == (int) var_id);
        
        o->neg = (lit < 0);
        o->var = var;
        o->clause = c;
    }
    
    qsort(c->occs, c->size, sizeof(Occ), compare_occurrence_by_level_then_var_id);
    
    for (int i = c->size - 1; i >= 0; i--) { // delete trailing universal variables
        Occ* o = &c->occs[i];
        if (o->var->scope->qtype == QUANTIFIER_UNIVERSAL) {
            c->size--;
        } else {
            break;
        }
    }
    
    for (int i = 0; i < c->size; i++) {
        // occ_init()
        Occ* o = &c->occs[i];
        // Update the occurrence list of the variable
        if (! o->neg) {
            vector_add(o->var->pos_occs, o);
        } else {
            vector_add(o->var->neg_occs, o);
        }
    }
    
    // register clause in matrix
    m->clause_num++;
    c->clause_id = (int) m->max_clause_id++;
    
    c->prev = NULL;
    c->next = m->first_clause;
    if (m->first_clause != NULL) {
        m->first_clause->prev = c;
    }
    m->first_clause = c;

    if (m->result == MATRIX_SATISFIABLE) {
        m->result = MATRIX_UNKNOWN;
    }
    
    return c;
}

MVar* matrix_add_variable_to_last_scope(Matrix* m, int var_id) {
    assert(var_id > 0);
    MScope* scope = matrix_get_last_scope(m);
    MVar* var = matrix_new_var(m, scope, var_id);
    vector_add(scope->vars, var);
    return var;
}

MVar* matrix_inc_max_var(Matrix* m) {
    m->max_var_id++;
    MVar* v = matrix_add_variable_to_last_scope(m, m->max_var_id);
    
    if (m->decision_level > 0) {
        Operation* op = matrix_new_operation(m);
        op->type = MATRIX_OP_NEW_MAX_VAR;
        op->var = v;
    }
    
    return v;
    
}

MClause* matrix_add_lit_undoable(Matrix* m, int lit) {
    MClause* c = matrix_add_lit(m, lit);
    
    if (debug_verbosity >= VERBOSITY_HIGH && (lit != 0 || c == NULL) && (lit == 0 || c != NULL)) {
        V3("Unusual clause added\n");
    }
    
    if (m->push_count > 0 && c != NULL) { // to avoid too many operations in the undo-chain
        Operation* op = matrix_new_operation(m);
        op->type = MATRIX_OP_ADD_CLAUSE;
        op->clause = c;
    }
    
    return c;
}

MClause* matrix_add_lit(Matrix* m, int lit) {
    if (lit != 0) {
        int_vector_add(m->new_clause, lit);
        return NULL;
    } else {
        MClause* c = matrix_new_clause(m, m->new_clause);
        int_vector_reset(m->new_clause);
        
        if (c != NULL && m->decision_level == NO_DECISION) {
            c->original = true;
            if (c->size == 0) {
                matrix_assign_result(m, MATRIX_UNSATISFIABLE);
            }
        }
        
        return c;
    }
}

MScope* matrix_get_last_scope(Matrix* m) {
    return vector_get(m->scopes, vector_count(m->scopes) - 1);
}

void matrix_free_scope(MScope* scope) {
    vector_free(scope->vars);
    free(scope);
}

void matrix_free_clause(MClause* c) {
    free(c->occs);
    free(c);
}

void matrix_free(Matrix* m) {
    MClause* next = NULL;
    for (MClause* c = m->first_clause; c != NULL; c = next) {
        next = c->next;
        matrix_free_clause(c);
    }
    
    map_free(m->var_lookup);
    heap_free(m->variables_to_check_for_determinicity);
    heap_free(m->clauses_to_check);
    heap_free(m->variables_to_check);
    free(m->op_vector);
    
    for (unsigned i = 0 ; i < vector_count(m->scopes); i++) {
        MScope* s = vector_get(m->scopes, i);
        for (unsigned i = 0; i < vector_count(s->vars); i++) {
            MVar* v = vector_get(s->vars, i);
            if (v != NULL) {
                vector_free(v->pos_occs);
                vector_free(v->neg_occs);
                free(v);
            }
        }
        matrix_free_scope(s);
    }
    
    free(m);
}

// propagation

//// Checks whether the variable has an empty occurrence list and if so,
//// it adds the variable to the appropriate propagation queue.
//void check_empty_occurrence_lists(Matrix* m, MVar* var) {
//    
//    if (var->scope->qtype == QUANTIFIER_UNIVERSAL) {
//        return;
//    }
//    
//    bool pos_occs_empty = true;
//    for (unsigned i = 0; i < vector_count(var->pos_occs); i++) {
//        Occ* o = vector_get(var->pos_occs, i);
//        if (o->clause->satisfied_by != NULL) {
//            continue;
//        }
//        pos_occs_empty = false;
//        break;
//    }
//    
//    bool neg_occs_empty = true;
//    for (unsigned i = 0; i < vector_count(var->neg_occs); i++) {
//        Occ* o = vector_get(var->neg_occs, i);
//        if (o->clause->satisfied_by != NULL) {
//            continue;
//        }
//        neg_occs_empty = false;
//        break;
//    }
//    
//    if ((var->scope->qtype == QUANTIFIER_UNIVERSAL && neg_occs_empty)
//     || (var->scope->qtype == QUANTIFIER_EXISTENTIAL && pos_occs_empty)) {
//        V4("MVariable %d has an empty occurrence list and is therefore fixed as false.\n", var->var_id);
//        assert(var->pointed_to_in_implication_graph == NULL);
//        assert(var->cause == NO_CAUSE);
//        var->cause = PURE_LITERAL;
//        matrix_propagation(m, var, -1); // true means negated
//    } else if ((var->scope->qtype == QUANTIFIER_UNIVERSAL && pos_occs_empty)
//            || (var->scope->qtype == QUANTIFIER_EXISTENTIAL && neg_occs_empty)) {
//        V4("MVariable %d has an empty occurrence list and is therefore fixed as true.\n", var->var_id);
//        assert(var->pointed_to_in_implication_graph == NULL);
//        assert(var->cause == NO_CAUSE);
//        var->cause = PURE_LITERAL;
//        matrix_propagation(m, var, 1); // false means not negated
//    }
//}

// check for propagations
void check_clause(Matrix* m, MClause* c) {
    V4("Checking clause %d.\n", c->clause_id);
    assert(m->result == MATRIX_UNKNOWN);
    assert( ! is_clause_satisfied(c));

    // right of c->max_scope there cannot be active literals, going right to left in the array of occurrences
    
    Occ* first_active = &c->occs[c->size - 1];
    while (first_active >= c->occs && ((first_active->var->value != 0)
                                       || (first_active->var->scope->qtype == QUANTIFIER_UNIVERSAL))) {
//        if (first_active->var->scope->qtype == QUANTIFIER_UNIVERSAL && is_active(first_active)) {
//            if (! first_active->var->needs_qbce_check) {
//                first_active->var->needs_qbce_check = true;
//                heap_push(m->variables_to_check, first_active->var);
//                V3("Pushing variable %d to check list.\n", first_active->var->var_id);
//            }
//        }
        first_active--;
    }
    if (first_active < c->occs) {
        V2("Detected empty clause %d.\n", c->clause_id);
        assert(m->conflicted_clause == NULL);
        m->conflicted_clause = c;
        matrix_assign_result(m, MATRIX_UNSATISFIABLE);
        return;
    }
    assert(first_active != NULL);
    assert(first_active->var->scope->qtype == QUANTIFIER_EXISTENTIAL);
    Occ* second_active = first_active;
    second_active--;
    while(second_active >= c->occs) {
        if (second_active->var->value == 0) {
            // no propagations to schedule, max_scope is updated to, so we can stop here.
            return;
        }
        second_active--;
    }
    if (second_active < c->occs) {
        second_active = NULL; // better safe than sorry
        assert(first_active->var->value == 0);
//        assert(first_active->var->pointed_to_in_implication_graph == NULL);
        assert(first_active->var->scope->qtype == QUANTIFIER_EXISTENTIAL);
        // clause has has exactly one literal
//        first_active->var->pointed_to_in_implication_graph = c;
        matrix_propagate_var(m, first_active->var, first_active->neg ? -1 : 1);
        return;
    }
    
    assert( ! is_clause_satisfied(c));
    assert(m->result == MATRIX_UNKNOWN);
    assert(first_active != NULL && first_active->var->scope->qtype == QUANTIFIER_EXISTENTIAL);
}

// Removes the clause that is satisfied by this occurrence
void matrix_clause_satisfied(Matrix* m, Occ* o) {
    MClause* c = o->clause;
    // The clause is satisfied and needs to be removed from all occurrence lists
    V4("Removing clause %d\n", c->clause_id);
    
//    for (Occ* occ = &c->occs[c->size - 1]; occ >= c->occs; occ--) {
//        if (is_active(occ)) {
//            if (! occ->var->needs_qbce_check) {
//                occ->var->needs_qbce_check = true;
//                heap_push(m->variables_to_check, occ->var);
//                V4("Pushing variable %d to QBCE check list.\n", occ->var->var_id);
//            }
//        }
//    }
    
    m->satisfied_clauses += 1;
    if (m->satisfied_clauses == m->clause_num) {
        matrix_assign_result(m, MATRIX_SATISFIABLE);
    }
    
    Operation* op = matrix_new_operation(m);
    op->type = MATRIX_OP_CLAUSE_SATISFIED;
    op->clause = c;
}

// Applies pure literal detection and universal reduction; then propagates.
// If the matrix is SATISFIED or UNSATISFIABLE, the propagation stops.
// This operation is not undoable. Call this method BEFORE building clausal abstractions, as their
// SAT-solvers will be inconsistent after this call.
void matrix_simplify(Matrix* m) {
    
    size_t assigned_vars = m->assigned_variables;
    
    vector_reset(m->clauses_to_check->vector);
    for (MClause* c = m->first_clause; c != NULL; c = c->next) {
        heap_push(m->clauses_to_check, c);
        c->needs_propagation_check = true;
    }
    
    matrix_propagate(m);
    assert(m->result != MATRIX_UNKNOWN  ||  heap_count(m->clauses_to_check) == 0);
    
    V2("Assigned %zu variables.\n", m->assigned_variables - assigned_vars);
    V2("Satisfied %zu clauses.\n", m->satisfied_clauses);
    V2("Removed %zu occs from occurrence lists.\n", m->removed_occurrences_from_occurrence_list);
}

// Checks all pending clauses in the heap of the matrix
void matrix_propagate(Matrix* m) {
    while ( heap_count(m->clauses_to_check) > 0  &&  m->result == MATRIX_UNKNOWN) {
        MClause* clause_to_check = heap_pop(m->clauses_to_check);
        assert(clause_to_check != NULL);
        assert(clause_to_check->needs_propagation_check);
        clause_to_check->needs_propagation_check = false;
        if (! is_clause_satisfied(clause_to_check)) {
            check_clause(m, clause_to_check);
        }
    }
    
    // flush propagation heap in case matrix result is clear
    while ( heap_count(m->clauses_to_check) > 0 ) {
        assert(m->result != MATRIX_UNKNOWN);
        MClause* clause_to_check = heap_pop(m->clauses_to_check);
        assert(clause_to_check != NULL);
        assert(clause_to_check->needs_propagation_check);
        clause_to_check->needs_propagation_check = false;
    }
}

//////////////// ASSUMPTIONS and BACKTRACKING

void matrix_assume(Matrix* m, int value, MVar* var) {
    assert(value == -1 || value == 1);
    assert(m->result != MATRIX_UNSATISFIABLE);
    assert(var->value == 0);
    
//    var->decision_level = m->cur_decision_level;
    matrix_propagate_var(m, var, value);
}

void matrix_decision_var(Matrix* m, MVar* v) {
    assert(!v->is_decision_var);
    assert(v->decision_level == NO_DECISION);
    
    Operation* op = matrix_new_operation(m);
    op->type = MATRIX_OP_DECISION;
    op->var = v;
    
    m->decision_level++;
    
    v->is_decision_var = true;
}

bool has_illegal_dependence(MClause* clause) {
    V4("LOOK AT ME: Shouldn't dependencies checked for the dependence levels instead of the quantifier levels?\n");
    assert(clause->unique_consequence_occ != NULL);
    Occ* last_occ = &clause->occs[clause->size-1];
    assert(last_occ->var->scope->qtype == QUANTIFIER_EXISTENTIAL);
    assert(last_occ >= clause->unique_consequence_occ);
    return last_occ->var->scope->level > clause->unique_consequence_occ->var->scope->level;
    
    // TODO: shouldn't it rather be the following? a comparison of dependency levels and qlvl of the uc (taken from cadet2)
//    assert(skolem_has_unique_consequence(s, c));
//    Lit uc_lit = skolem_get_unique_consequence(s, c);
//    MVar* uc_v = vector_get(qcnf->vars, lit_to_var(uc_lit));
//    for (unsigned i = 0; i < c->size - 1; i++) {
//        if (skolem_get_dependence_lvl(s, c->occs[i]) > uc_v->qlvl) {
//            return true;
//        }
//    }
//    return false;
}

size_t maximal_dependence_lvl(Matrix* m, MClause* c) {
    assert(c->unique_consequence_occ);
    size_t lvl = m->minimal_dependence_lvl;
    for (unsigned j = 0; j < c->size; j++) {
        Occ* clause_occ = &c->occs[j];
        MVar* other = clause_occ->var;
        if (clause_occ == c->unique_consequence_occ) {
            continue;
        }
        assert(other->dependence_level < NO_DEPENDENCE_LVL);
        if (lvl < other->dependence_level) {
            lvl = other->dependence_level;
        }
    }
    assert(lvl != NO_DEPENDENCE_LVL);
    return lvl;
}

// maximum of minimal_dependence_lvl of the matrix and the dependencies necessary accoding to the clauses.
size_t compute_dependence_lvl(Matrix* m, MVar* v) {
    assert(m->minimal_dependence_lvl != NO_DEPENDENCE_LVL);
    size_t max_lvl = m->minimal_dependence_lvl;
    for (unsigned i = 0; i < vector_count(v->pos_occs); i++) {
        Occ* o = vector_get(v->pos_occs, i);
        if (o->clause->unique_consequence_occ == o && ! has_illegal_dependence(o->clause)) {
            size_t lvl = maximal_dependence_lvl(m, o->clause);
            if (max_lvl < lvl) {
                max_lvl = lvl;
            }
        }
    }
    for (unsigned i = 0; i < vector_count(v->neg_occs); i++) {
        Occ* o = vector_get(v->neg_occs, i);
        if (o->clause->unique_consequence_occ == o && ! has_illegal_dependence(o->clause)) {
            size_t lvl = maximal_dependence_lvl(m, o->clause);
            if (max_lvl < lvl) {
                max_lvl = lvl;
            }
        }
    }
//    assert(v->dependence_level != 0 || is_constant(v));
    return max_lvl;
}

void matrix_deterministic_var(Matrix* m, MVar* v) {
    assert(v->decision_level == NO_DECISION);
    v->decision_level = (unsigned) m->decision_level;
    
    v->dependence_level = compute_dependence_lvl(m, v);
    
    Operation* op = matrix_new_operation(m);
    op->type = MATRIX_OP_DETERMINISTIC_VAR;
    op->var = v;
}

void matrix_push_milestone(Matrix* m) {
    Operation* op = matrix_new_operation(m);
    op->type = MATRIX_OP_MILESTONE;
    m->push_count += 1;
}

void matrix_remove_clause(Matrix* m, MClause* c) {
    m->clause_num--;
//    if (is_clause_satisfied(c)) {
//        m->satisfied_clauses--;
//    }
    
    if (c->prev != NULL) {
        c->prev->next = c->next;
    }
    if (c->next != NULL) {
        c->next->prev = c->prev;
    }
    
    if (m->first_clause == c) {
        m->first_clause = c->next;
    }
    
    for (unsigned i = 0; i < c->size; i++) {
        Occ* o = &c->occs[i];
        vector* var_occs = o->neg ? o->var->neg_occs : o->var->pos_occs;
        vector_remove_unsorted(var_occs, o);
    }
    
    matrix_free_clause(c);
}

void matrix_undo_operation(Matrix* m, Operation* op) {
    switch (op->type) {
        case MATRIX_OP_ASSIGN_VAR:
            V4("Restoring variable %d\n", op->var->var_id);
            assert(op->var->value == 1 || op->var->value == -1);
            
//            op->var->pointed_to_in_implication_graph = NULL;
            op->var->value = 0;
            
            // Don't do this here, but only in determinicity assignments (ASSIGN_VAR currently only used in preprocessing):
//            op->var->decision_level = NO_DECISION;
//            op->var->dependence_level = NO_DEPENDENCE_LVL;
            
            break;
            
        case MATRIX_OP_CLAUSE_SATISFIED:
            V4("Restoring clause %d\n", op->clause->clause_id);
            m->satisfied_clauses -= 1;
            
            MClause* c = op->clause;
            if (debug_verbosity >= VERBOSITY_HIGH) {
                // check max_scope invariant of max_scope
                for (Occ* o = &c->occs[c->size - 1]; ++o <= &c->occs[c->size - 1];) {
                    assert(o->var->value != 0);
                }
            }
            break;
            
        case MATRIX_OP_ASSIGN_MATRIX_RESULT:
            m->conflicted_clause = NULL;
            m->result = op->previous_result;
            break;
            
        case MATRIX_OP_ADD_CLAUSE:
            
            matrix_remove_clause(m, op->clause);
            
            break;
            
        case MATRIX_OP_NEW_MAX_VAR:
            assert(op->var->var_id == m->max_var_id);
            assert(op->var->is_helper); // just for consistency (as of Jan 3rd 2016); this may change later
            m->max_var_id--;
            assert(vector_count(op->var->pos_occs) == 0);
            assert(vector_count(op->var->neg_occs) == 0);
            assert(! op->var->is_decision_var);
            assert(op->var->decision_level == NO_DECISION);
            assert(vector_get(op->var->scope->vars, vector_count(op->var->scope->vars) - 1) == op->var);
            vector_remove_last_element(op->var->scope->vars);
            map_remove(m->var_lookup, op->var->var_id);
            free(op->var);
            break;

        case MATRIX_OP_DETERMINISTIC_VAR:
            assert(op->var->scope->qtype == QUANTIFIER_EXISTENTIAL);
            assert(op->var->decision_level > 0);
            op->var->decision_level = NO_DECISION;
            op->var->dependence_level = NO_DEPENDENCE_LVL;
            
            // unassign directions in clauses that point to OTHER variables
            for (unsigned i = 0; i < vector_count(op->var->pos_occs); i++) {
                Occ* o = vector_get(op->var->pos_occs, i);
                if (o->clause->unique_consequence_occ != NULL && o->clause->unique_consequence_occ != o) {
                    assert(o->clause->unique_consequence_occ->var->decision_level == NO_DECISION);
                    assert(o->clause->unique_consequence_occ->var->dependence_level == NO_DEPENDENCE_LVL);
                    o->clause->unique_consequence_occ = NULL;
                }
            }

            for (unsigned i = 0; i < vector_count(op->var->neg_occs); i++) {
                Occ* o = vector_get(op->var->neg_occs, i);
                if (o->clause->unique_consequence_occ != NULL && o->clause->unique_consequence_occ != o) {
                    assert((o->clause->unique_consequence_occ->var->decision_level == NO_DECISION
                                && o->clause->unique_consequence_occ->var->dependence_level == NO_DEPENDENCE_LVL)
                           || o->clause->unique_consequence_occ->var->dependence_level > op->var->dependence_level);
                    o->clause->unique_consequence_occ = NULL;
                }
            }
            
            if (! op->var->is_helper && ! op->var->needs_determinicity_check) {
                V3("; queueing variable %d", op->var->var_id);
                op->var->needs_determinicity_check = true;
                heap_push(m->variables_to_check_for_determinicity, op->var);
            }
            
            break;
            
        case MATRIX_OP_QBCE_ELIMINATION:
            op->clause->blocked = false;
            break;
            
        case MATRIX_OP_DECISION:
            op->var->is_decision_var = false;
            m->decision_level--;
            break;
            
        default :
            NOT_IMPLEMENTED();
    }
}

void matrix_pop_milestone(Matrix* m) {
    V4("Popping milestone %d\n", m->push_count);
    assert(m->push_count > 0);
    Operation* op;
    // Don't know how to write the following loop head more elegant. The op_count must be decreased by one, then op must be assigned the new operation, then we must check whether the operation happened to be a milestone.
    size_t i = 0;
    while ((op = &m->op_vector[ -- m->op_count])->type != MATRIX_OP_MILESTONE) {
        i++;
        matrix_undo_operation(m, op);
        assert(m->op_count > 0);
    }
    V3("Popped %zu items.\n", i);
    m->push_count -= 1;
}



//////////////////////// MATRIX CLEANUP  ///////////////////////////////

Matrix* matrix_cleanup(Matrix* old) {
    
    Matrix* new = matrix_init();
    
    for (unsigned i = 0; i < vector_count(old->scopes); i++) {
        MScope* s = vector_get(old->scopes, i);
        
        if (vector_count(s->vars) == 0) {
            continue;
        }
        bool scope_empty = true;
        
        for (unsigned j = 0; j < vector_count(s->vars); j++) {
            MVar* v = vector_get(s->vars, j);
            if (scope_empty) {
                matrix_new_scope(new, s->qtype);
                scope_empty = false;
            }
            MVar* new_var = matrix_add_variable_to_last_scope(new, v->var_id);
            new_var->value = v->value;
            new_var->dependence_level = v->dependence_level;
            assert(new_var->dependence_level == 0 || new_var->dependence_level == NO_DEPENDENCE_LVL || new_var->scope->qtype == QUANTIFIER_UNIVERSAL);
        }
    }
    
    MClause* last_clause = NULL;
    for (last_clause = old->first_clause; last_clause != NULL && last_clause->next != NULL; last_clause = last_clause->next) {}
    
    for (MClause* c = last_clause; c != NULL; c = c->prev) {
        if (is_clause_satisfied(c) || c->blocked) {
            continue;
        }
        
        for (int j = 0; j < c->size; j++) {
            Occ* o = &c->occs[j];
            if (o->var->value != 0) {
                continue;
            }
            matrix_add_lit(new, matrix_get_lit(o));
        }
        
        MClause* c_new = matrix_add_lit(new, 0);
        assert(c);
        c_new->original = c->original;
    }
    return new;
}



////////////////////// PRINTING /////////////////////////

void matrix_print_clause(MClause* c, FILE* f) {
    for (int i = 0; i < c->size; i++) {
        Occ* o = & c->occs[i];
        if (o->var->value != 0) {
            continue;
        }
        fprintf(f, "%d ", matrix_get_lit(o));
    }
    fprintf(f, "0\n");
}

void matrix_print_qdimacs(Matrix* m) {
    matrix_print_qdimacs_file(m, stdout);
}

void matrix_print_qdimacs_file(Matrix* m, FILE* f) {
    int max_var_id = 0;
    for (unsigned i = 0 ; i < vector_count(m->scopes); i++) {
        MScope* s = vector_get(m->scopes, i);
        for (unsigned j = 0; j < vector_count(s->vars); j++) {
            MVar* var = vector_get(s->vars, j);
            if (var->value == 0 && var->var_id > max_var_id) {
                max_var_id = var->var_id;
            }
        }
    }
    
    fprintf(f, "p cnf %d %d\n", max_var_id, (int)m->clause_num - (int)m->satisfied_clauses);
    
    for (unsigned i = 0; i < vector_count(m->scopes); i++) {
        MScope* scope = vector_get(m->scopes, i);
        if (vector_count(scope->vars) == 0) {
            continue;
        }
        fprintf(f, "%c ", scope->qtype == QUANTIFIER_EXISTENTIAL ? 'e' : 'a');
        for (unsigned i = 0; i < vector_count(scope->vars); i++) {
            MVar* var = vector_get(scope->vars, i);
            if (var->value == 0) {
                fprintf(f, "%d ", var->var_id);
            }
        }
        fprintf(f, "0\n");
    }
    
    MClause* last_clause = NULL;
    for (last_clause = m->first_clause; last_clause != NULL && last_clause->next != NULL; last_clause = last_clause->next) {}
    
    for (MClause* c = last_clause; c != NULL; c = c->prev) {
        if (! is_clause_satisfied(c)) {
            matrix_print_clause(c, f);
        }
    }
}

void matrix_print_clause_debug(MClause* c) {
    for (int i = 0; i < c->size; i++) {
        Occ* o = & c->occs[i];
        if (o->var->value != 0) {
            printf("(%d) ", matrix_get_lit(o));
        } if (c->unique_consequence_occ == o) {
            // skip
        } else {
            if (o->var->dependence_level != NO_DEPENDENCE_LVL) {
                printf("[%d] ", matrix_get_lit(o));
            } else {
                if (o->var->scope->qtype == QUANTIFIER_UNIVERSAL) {
                    printf("u%d ", matrix_get_lit(o));
                } else {
                    printf("%d ", matrix_get_lit(o));
                }
            }
        }
    }
    if (c->unique_consequence_occ) {
        if (c->unique_consequence_occ->var->dependence_level != NO_DEPENDENCE_LVL) {
            printf(" -> [%d]", matrix_get_lit(c->unique_consequence_occ));
        } else {
            printf(" -> %d", matrix_get_lit(c->unique_consequence_occ));
        }
        
    }
    if (is_clause_satisfied(c)) {
        printf(" sat!");
    }
    
    if (c->unconflicting) {
        printf(" unconflicted");
    }
    printf("\n");
}

void matrix_print_debug(Matrix* m) {
    int max_var_id = 0;
    for (unsigned i = 0 ; i < vector_count(m->scopes); i++) {
        MScope* s = vector_get(m->scopes, i);
        for (unsigned j = 0; j < vector_count(s->vars); j++) {
            MVar* var = vector_get(s->vars, j);
            if (var->value == 0 && var->var_id > max_var_id) {
                max_var_id = var->var_id;
            }
        }
    }

    printf("p cnf %d %d\n", max_var_id, (int)m->clause_num - (int)m->satisfied_clauses);
    
    for (unsigned i = 0; i < vector_count(m->scopes); i++) {
        MScope* scope = vector_get(m->scopes, i);
        printf("%c ", scope->qtype == QUANTIFIER_EXISTENTIAL ? 'e' : 'a');
        for (unsigned i = 0; i < vector_count(scope->vars); i++) {
            MVar* var = vector_get(scope->vars, i);
            if (var->value == 0) {
                printf("%d ", var->var_id);
            }
        }
        printf("0\n");
    }
    
    for (MClause* c = m->first_clause; c != NULL; c = c->next) {
        printf("MClause %d: ", c->clause_id);
        matrix_print_clause_debug(c);
    }
}
