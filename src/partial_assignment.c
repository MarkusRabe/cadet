//
//  partial_assignment.c
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "partial_assignment.h"
#include "log.h"
#include "util.h"

#include <assert.h>
#include <stdint.h>

struct PA_UNDO_PAIR {
    unsigned var_id;
    int previous_value;
};
union PA_UNDO_PAIR_UNION {
    struct PA_UNDO_PAIR pup;
    void* data;
};

PartialAssignment* partial_assignment_init(QCNF* qcnf) {
    PartialAssignment* pa = malloc(sizeof(PartialAssignment));
    pa->qcnf = qcnf;
    pa->clauses_to_check = worklist_init(qcnf_compare_clauses_by_size);
    pa->assigned_variables = 0;
    pa->conflicted_clause = NULL;
    pa->conflicted_var = 0;
    pa->stack = stack_init(partial_assignment_undo);
    pa->vals = val_vector_init();
    pa->causes = vector_init();
    
    pa->decision_lvl = 0;
    pa->decision_lvls = int_vector_init();
    
    pa->conflicts = 0;
    pa->propagations = 0;
    
    Clause_Iterator ci = qcnf_get_clause_iterator(qcnf); Clause* c = NULL;
    while ((c = qcnf_next_clause(&ci)) != NULL) {
        if (c->size == 1) {
            worklist_push(pa->clauses_to_check, c);
        }
    }
    return pa;
}

void partial_assignment_free(PartialAssignment* pa) {
    worklist_free(pa->clauses_to_check);
    stack_free(pa->stack);
    val_vector_free(pa->vals);
#ifdef DEBUG_PARTIAL_ASSIGNMENT
    vector_free(pa->vals_debug);
#endif
    vector_free(pa->causes);
    free(pa);
}

void partial_assignment_pop(PartialAssignment* pa) {
    worklist_reset(pa->clauses_to_check);
    pa->decision_lvl -= 1;
    stack_pop(pa->stack, pa);
}
void partial_assignment_push(PartialAssignment* pa) {
    pa->decision_lvl += 1;
    stack_push(pa->stack);
}

bool partial_assignment_is_conflicted(PartialAssignment* pa) {
    return pa->conflicted_clause != NULL;
}

VAL partial_assignment_get_val(PartialAssignment* pa, unsigned idx) {
    if (idx >= val_vector_count(pa->vals)) {
        return top;
    }
    return (VAL) val_vector_get(pa->vals, idx);
}

void partial_assignment_enlarge_decision_lvls(PartialAssignment* pa, unsigned idx) {
    while (idx >= int_vector_count(pa->decision_lvls)) {
        int_vector_add(pa->decision_lvls, 0);
    }
}
void partial_assignment_set_dlvl(PartialAssignment* pa, unsigned var_id) {
    partial_assignment_enlarge_decision_lvls(pa, var_id);
    
    unsigned dlvl = partial_assignment_get_decision_lvl(pa, var_id);
    if (dlvl != 0) {
        union PA_UNDO_PAIR_UNION pupu;
        pupu.pup.var_id = var_id;
        pupu.pup.previous_value = (int) dlvl;
        stack_push_op(pa->stack, PA_OP_DLVL, pupu.data);
    }
    
    int_vector_set(pa->decision_lvls, var_id, (int)pa->decision_lvl);
}

void partial_assignment_enlarge_val_vector(val_vector* vv, unsigned idx) {
    while (idx >= val_vector_count(vv)) {
        val_vector_add(vv, top);
    }
}
void partial_assignment_set_val(PartialAssignment* pa, unsigned var_id, VAL new) {
    assert(var_id >= 0);
    partial_assignment_enlarge_val_vector(pa->vals, var_id);
    val_vector_set(pa->vals, var_id, new);
}

Lit partial_assignment_is_clause_satisfied(PartialAssignment* pa, Clause* c) {
    for (int i = 0; i < c->size; i++) {
        VAL v = partial_assignment_get_val(pa, lit_to_var(c->occs[i]));
        if (v == (c->occs[i] > 0 ? tt : ff)) {
            return c->occs[i];
        }
    }
    return 0;
}

void update_clause_worklist(PartialAssignment* pa, QCNF* qcnf, int unassigned_lit) {
    Var* v = var_vector_get(qcnf->vars, lit_to_var(unassigned_lit));
    vector* occs = unassigned_lit > 0 ? &v->neg_occs : &v->pos_occs;
    for (unsigned i = 0; i < vector_count(occs); i++) {
        worklist_push(pa->clauses_to_check, vector_get(occs, i));
    }
}

void partial_assignment_go_into_conflict_state(PartialAssignment* pa, Clause* conflicted_clause, unsigned conflicted_var) {
    assert(conflicted_clause != NULL);
    assert(pa->conflicted_clause == NULL);
    assert(pa->conflicted_var == 0);
    pa->conflicts++;
    pa->conflicted_clause = conflicted_clause;
    pa->conflicted_var = conflicted_var;
    stack_push_op(pa->stack, PA_OP_CONFLICT, (void*) pa->conflicted_clause);
    V3("Conflict in partial assignment domain for clause %u.\n", pa->conflicted_clause->clause_idx);
}

void partial_assignment_assign_value(PartialAssignment* pa, Lit lit) {
        V4("Partial assignment assign value %d.\n",lit);
    
    unsigned var_id = lit_to_var(lit);
    
    VAL val = partial_assignment_get_val(pa, var_id);
    assert(val == top);    
    union PA_UNDO_PAIR_UNION pupu;
    pupu.pup.var_id = var_id;
    pupu.pup.previous_value = partial_assignment_get_val(pa, val);
    stack_push_op(pa->stack, PA_OP_ASSIGN, (void*) pupu.data);
    
    VAL new_val = lit > 0 ? tt : ff;
    partial_assignment_set_val(pa, var_id, new_val);
    
    assert(partial_assignment_get_decision_lvl(pa, var_id) == 0);
    partial_assignment_set_dlvl(pa, var_id);
    
    pa->assigned_variables++;
    update_clause_worklist(pa, pa->qcnf, lit);
    
//    if (val == oposite) {
//        abortif(true, "This is the wrong place to handle conflicts");
//        partial_assignment_go_into_conflict_state(pa, partial_assignment_get_relevant_clause(pa, var_id), var_id);
//    }
}

void partial_assignment_propagate_clause(PartialAssignment* pa, Clause* c) {
    Lit unassigned_lit = 0;
    bool contains_universals = false;
    for (int i = 0; i < c->size; i++) {
        VAL v = partial_assignment_get_val(pa, lit_to_var(c->occs[i]));
        assert(v != bottom);
        
        if (v == (c->occs[i] > 0 ? tt : ff)) {
            // this literal satisfies the clause
            return;
        }
        if (v == top) {
            if (unassigned_lit != 0 || contains_universals) {
                // two unassigned existentials; clause cannot propagate
                return;
            }
            unassigned_lit = c->occs[i];
        }
    }
    
    if (unassigned_lit == 0) { // conflict
        partial_assignment_go_into_conflict_state(pa,c,0); // leaving conflicted var 0, as no unique var can be determined
    } else { // assign value
        assert(! contains_universals);
//        V4("Propagating variable %d.\n",unassigned_lit);
        pa->propagations++;
        partial_assignment_assign_value(pa, unassigned_lit);
        
        while (vector_count(pa->causes) <= lit_to_var(unassigned_lit)) {
            vector_add(pa->causes, NULL);
        }
        vector_set(pa->causes, lit_to_var(unassigned_lit), c);
    }
}

void partial_assignment_propagate(PartialAssignment* pa) {
    V4("Propagating partial assignments\n");
    while (worklist_count(pa->clauses_to_check) > 0) {
        if (partial_assignment_is_conflicted(pa)) {
            break;
        }
        Clause* c = worklist_pop(pa->clauses_to_check);
        partial_assignment_propagate_clause(pa, c);
    }
    if (partial_assignment_is_conflicted(pa)) {
        worklist_free(pa->clauses_to_check);
        pa->clauses_to_check = worklist_init(qcnf_compare_clauses_by_size);
        return;
    }
}

// INTERACTION WITH CONFLICT ANALYSIS

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wunused-parameter"
bool partial_assignment_is_legal_dependence(void* s, unsigned var_id, unsigned depending_on) {
    return true;
}
#pragma clang diagnostic pop

int partial_assignment_get_value_for_conflict_analysis(void* domain, Lit lit) {
    assert(lit != 0);
    VAL val = partial_assignment_get_val((PartialAssignment*) domain, lit_to_var(lit));
    assert(val != bottom);
    assert(val >= 0);
    assert(bottom == 3);
    assert(tt == 2);
    assert(ff == 1);
    assert(top == 0);
    assert((-3 % 3) == 0);
    int x = val == top ? 0 : ((2 * val) - 3);
    assert(val == ff && x == -1 || val == top && x == 0 || val == tt && x == 1);
    return lit > 0 ? x : -x;
}

bool partial_assignment_is_relevant_clause(void* domain, Clause* c, Lit lit) {
    PartialAssignment* pa = (PartialAssignment*) domain;
    return vector_count(pa->causes) > lit_to_var(lit) && c == vector_get(pa->causes, lit_to_var(lit));
}

Clause* partial_assignment_get_relevant_clause(void* domain, unsigned var_id) {
    PartialAssignment* pa = (PartialAssignment*) domain;
    if (vector_count(pa->causes) > var_id) {
        return vector_get(pa->causes, var_id);
    } else {
        return NULL;
    }
}

unsigned partial_assignment_get_decision_lvl(void* domain, unsigned var_id) {
    PartialAssignment* pa = (PartialAssignment*) domain;
    if (var_id >= int_vector_count(pa->decision_lvls)) {
        return 0;
    }
    return (unsigned) int_vector_get(pa->decision_lvls, var_id);
}

// Register new clauses

void partial_assignment_new_clause(PartialAssignment* pa, Clause* c) {
    worklist_push(pa->clauses_to_check, c);
}


// PRINTING

void partial_assignment_print_statistics(PartialAssignment* pa) {
    V1("Partial assignment statistics:\n");
    V1("  Propagations: %zu\n",pa->propagations);
    V1("  Conflicts: %zu\n",pa->conflicts);
    V1("  Current assignments: %zu\n",pa->assigned_variables);
}

void pa_print_debug_info(PartialAssignment* pa) {
    assert(pa);
#ifdef DEBUG_PARTIAL_ASSIGNMENT
    V1("PA state: \n"
       "  is conflicted: %u\n  vals: ", pa->conflicted);
    unsigned j = 0;
    for (unsigned i = 0; i < vector_count(pa->vals_debug); i++) {
        VAL val = partial_assignment_get_val(pa, i);
        if (val) {
            V1("%u -> %d", i, partial_assignment_get_val(pa, i));
            if (i + 1 != vector_count(pa->vals_debug)) {
                V1(", ");
            }
            if (j % 8 == 7) {
                V1("\n  ");
            }
            j++;
        }
        if (i + 1 == vector_count(pa->vals_debug)) {
            V1("\n  ");
        }
            
    }
    V1("\n  Worklist count: %u\n", worklist_count(pa->clauses_to_check));
#endif
}

// PRIVATE FUNCTIONS

void partial_assignment_undo(void* parent, char type, void* obj) {
    PartialAssignment* pa = (PartialAssignment*) parent;
    union PA_UNDO_PAIR_UNION pupu;
    unsigned var_id = 0;
    switch ((PA_OPERATION) type) {
        case PA_OP_ASSIGN:
            assert(obj != NULL);
            pupu.data = obj;
            var_id = pupu.pup.var_id;
            
            assert(partial_assignment_get_val(pa, var_id) == tt || partial_assignment_get_val(pa, var_id) == ff);
            partial_assignment_set_val(pa, var_id, (VAL) pupu.pup.previous_value);
            int_vector_set(pa->decision_lvls, var_id, 0);
            if (vector_count(pa->causes) > var_id) { // could be decision var! so this is not always true
                vector_set(pa->causes, var_id, NULL);
            }
            pa->assigned_variables--;
            break;
            
        case PA_OP_CONFLICT:
            assert(pa->conflicted_clause == (Clause*) obj);
            pa->conflicted_clause = NULL;
            pa->conflicted_var = 0;
            break;
        
        case PA_OP_DLVL:
            assert(obj != NULL);
            pupu.data = obj;
            var_id = pupu.pup.var_id;
            int_vector_set(pa->decision_lvls, var_id, pupu.pup.previous_value);
            break;
            
        default:
            V0("Unknown undo operation in partial_assignment.c: %d\n",(int) type);
            NOT_IMPLEMENTED();
    }
}

bool partial_assignment_is_antecedent_satisfied(PartialAssignment* pa, Clause* c, Lit consequence) {
    assert(qcnf_contains_literal(c, consequence));
    for (unsigned i = 0; i < c->size; i++) {
        Lit l = c->occs[i];
        if (l != consequence && partial_assignment_get_value_for_conflict_analysis(pa, l) != -1) {
            return false;
        }
    }
    return true;
}

//void partial_assignment_print(PartialAssignment* pa) {
//    NOT_IMPLEMENTED();
//}
