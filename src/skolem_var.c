//
//  skolem_var.c
//  cadet
//
//  Created by Markus Rabe on 27/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#include "skolem_var.h"
#include "skolem.h"
#include "log.h"
#include "c2_traces.h"
#include "c2_rl.h"

struct DEPENDENCECY_UPDATE;
typedef struct DEPENDENCECY_UPDATE DEPENDENCECY_UPDATE;
struct DEPENDENCECY_UPDATE {
    unsigned var_id;
    int_vector* dependencies;
};

skolem_var skolem_get_info(Skolem* s, unsigned var_id) {
    assert(var_id != 0);
    skolem_enlarge_skolem_var_vector(s, var_id);
    assert(skolem_var_vector_get(s->infos, var_id) != NULL);
    return *skolem_var_vector_get(s->infos, var_id);
}

unsigned skolem_get_decision_lvl_for_conflict_analysis(void* domain, unsigned var_id) {
    Skolem* s = (Skolem*) domain;
    if (skolem_get_constant_value(s, (Lit) var_id) != 0) {
        return skolem_get_dlvl_for_constant(s, var_id);
    } else {
        return skolem_get_decision_lvl(s, var_id);
    }
}
unsigned skolem_get_decision_lvl(Skolem* s, unsigned var_id) {
    assert(var_id < var_vector_count(s->qcnf->vars));
    skolem_enlarge_skolem_var_vector(s, var_id);
    assert(skolem_is_deterministic(s, var_id));
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    return sv->decision_lvl;
}
unsigned skolem_is_decision_var(Skolem* s, unsigned var_id) {
    assert(var_id < var_vector_count(s->qcnf->vars));
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    return sv->decision_pos || sv->decision_neg;
}
int skolem_get_decision_val(Skolem* s, unsigned var_id) {
    assert(var_id < var_vector_count(s->qcnf->vars));
    assert(skolem_is_deterministic(s, var_id));
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    int res = sv->decision_pos - sv->decision_neg;
    assert(res == 1 || res == -1 || res == 0);
    return res;
}
int skolem_get_pure_val(Skolem* s, unsigned var_id) {
    assert(var_id < var_vector_count(s->qcnf->vars));
    assert(skolem_is_deterministic(s, var_id));
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    int res = sv->pure_pos - sv->pure_neg;
    assert(res == 1 || res == -1 || res == 0);
    return res;
}
unsigned skolem_get_dlvl_for_constant(Skolem* s, unsigned var_id) {
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    return sv->dlvl_for_constant;
}
unsigned skolem_get_reason_for_constant(Skolem* s, unsigned var_id) {
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    return sv->reason_for_constant;
}

void skolem_print_skolem_var(Skolem* s, skolem_var* si, unsigned indent) {
    for (unsigned i = 0; i < indent; i++) {
        V1(" ");
    }
    V1("Skolem info:\n");
    for (unsigned i = 0; i < indent; i++) {
        V1(" ");
    }
    V1("pos_lit %d, neg_lit %d\n", si->pos_lit, si->neg_lit);
    for (unsigned i = 0; i < indent; i++) {
        V1(" ");
    }
    V1("det %d, pure_pos %d, pure_neg %d\n", si->deterministic, si->pure_pos, si->pure_neg);
    for (unsigned i = 0; i < indent; i++) {
        V1(" ");
    }
    V1("Dependencies: ");
    if (!qcnf_is_DQBF(s->qcnf)) {
        V1("%u\n", si->dep.dependence_lvl);
    } else {
        int_vector_print(si->dep.dependencies);
    }
    for (unsigned i = 0; i < indent; i++) {
        V1(" ");
    }
}


void skolem_enlarge_skolem_var_vector(Skolem* s, unsigned var_id) {
    skolem_var sv;
    
    // undoable portion of skolem_vars
    sv.pos_lit = - s->satlit_true;
    sv.neg_lit = - s->satlit_true;
    sv.pure_pos = 0;
    sv.pure_neg = 0;
    sv.deterministic = 0;
    sv.decision_pos = 0;
    sv.decision_neg = 0;
    
    sv.depends_on_decision_satlit = - s->satlit_true;
    
    sv.dep = s->empty_dependencies;
    
    // permanent portion
    sv.decision_lvl = 0;
    sv.conflict_potential = s->magic.initial_conflict_potential;
    sv.reason_for_constant = INT_MAX;
    sv.dlvl_for_constant = 0;
    
    // add this sv to the var_vector
    while (skolem_var_vector_count(s->infos) <= var_id) {
        skolem_var_vector_add(s->infos, sv);
    }
}

void skolem_update_reason_for_constant(Skolem* s, unsigned var_id, unsigned clause_id, unsigned dlvl) {
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    
    // we currently want to set it at most once, the next three checks ensure that
    assert(sv->reason_for_constant == INT_MAX);
    assert(sv->dlvl_for_constant == 0);
    assert(clause_id != UINT_MAX || dlvl != 0);
    
    V4("Setting reason %d for constant for var %u\n", clause_id, var_id);
    union skolem_undo_union suu;
    suu.sus.var_id = var_id;
    suu.sus.val = (int) sv->reason_for_constant;
    stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_REASON_FOR_CONSTANT, suu.ptr);
    sv->reason_for_constant = clause_id;
    sv->dlvl_for_constant = dlvl;
}

void skolem_undo_reason_for_constant(Skolem* s, void* data) {
    union skolem_undo_union suu;
    suu.ptr = data;
    skolem_var* sv = skolem_var_vector_get(s->infos, suu.sus.var_id);
    assert(suu.sus.val == INT_MAX); // currently reasons for constant are just set once.
    sv->reason_for_constant = (unsigned) suu.sus.val;
    sv->dlvl_for_constant = 0;
}

void skolem_update_decision_lvl(Skolem* s, unsigned var_id, unsigned dlvl) {
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    assert(sv->decision_lvl == 0); // we currently want decision levels to set just once, because it also serves as the information when the variable first became deterministic
    
    if (dlvl != sv->decision_lvl) {
        V4("Setting decision lvl %d for var %u\n", dlvl, var_id);
        union skolem_undo_union suu;
        suu.sus.var_id = var_id;
        suu.sus.val = (int) sv->decision_lvl;
        stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_DECISION_LVL, suu.ptr);
        sv->decision_lvl = dlvl;
    }
}

void skolem_undo_decision_lvl(Skolem* s, void* data) {
    union skolem_undo_union suu;
    suu.ptr = data;
    skolem_var* sv = skolem_var_vector_get(s->infos, suu.sus.var_id);
    sv->decision_lvl = (unsigned) suu.sus.val;
}

void skolem_update_pos_lit(Skolem* s, unsigned var_id, int pos_lit) {
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    if (pos_lit != sv->pos_lit) {
        V4("Setting pos_lit %d for var %u\n", pos_lit, var_id);
        union skolem_undo_union suu;
        suu.sus.var_id = var_id;
        suu.sus.val = sv->pos_lit;
        stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_POS_LIT, suu.ptr);
        sv->pos_lit = pos_lit;
        
        if (sv->neg_lit == s->satlit_true) {
            c2_rl_update_constant_value(suu.sus.var_id, 1);
        }
    }
}

void skolem_update_neg_lit(Skolem* s, unsigned var_id, int neg_lit) {
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    if (neg_lit != sv->neg_lit) {
        V4("Setting neg_lit %d for var %u\n", neg_lit, var_id);
        union skolem_undo_union suu;
        suu.sus.var_id = var_id;
        suu.sus.val = sv->neg_lit;
        stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_NEG_LIT, suu.ptr);
        sv->neg_lit = neg_lit;
        
        if (sv->neg_lit == s->satlit_true) {
            c2_rl_update_constant_value(suu.sus.var_id, -1);
        }
    }
}
void skolem_update_satlit(Skolem* s, Lit lit, int new_satlit) {
    if (lit > 0) {
        skolem_update_pos_lit(s, lit_to_var(lit), new_satlit);
    } else {
        skolem_update_neg_lit(s, lit_to_var(lit), new_satlit);
    }
}

void skolem_update_pure_pos(Skolem* s, unsigned var_id, unsigned pure_pos) {
    assert(pure_pos == 0 || pure_pos == 1);
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    if (sv->pure_pos != pure_pos) {
        V4("Setting pure_pos %d for var %u\n", pure_pos, var_id);
        union skolem_undo_union suu;
        suu.sus.var_id = var_id;
        suu.sus.val = sv->pure_pos;
        stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_PURE_POS, suu.ptr);
        sv->pure_pos = pure_pos;
    }
}
void skolem_update_pure_neg(Skolem* s, unsigned var_id, unsigned pure_neg) {
    assert(pure_neg == 0 || pure_neg == 1);
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    if (sv->pure_neg != pure_neg) {
        V4("Setting pure_neg %d for var %u\n", pure_neg, var_id);
        union skolem_undo_union suu;
        suu.sus.var_id = var_id;
        suu.sus.val = sv->pure_neg;
        stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_PURE_NEG, suu.ptr);
        sv->pure_neg = pure_neg;
    }
}
void skolem_update_deterministic(Skolem* s, unsigned var_id) {
    if (skolem_is_deterministic(s, var_id)) {
        return;
    }
    
    int_vector_add(s->determinization_order, (int) var_id);
    c2_rl_update_D(var_id, true);
    
    V4("Setting var %u deterministic\n", var_id);
    union skolem_undo_union suu;
    suu.sus.var_id = var_id;
    suu.sus.val = skolem_is_deterministic(s, var_id);
    stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_DETERMINISTIC, suu.ptr);
    
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    sv->deterministic = 1;
}
void skolem_update_decision(Skolem* s, Lit lit) {
    int_vector_add(s->decisions, lit);
    
    unsigned var_id = lit_to_var(lit);
    int val = lit>0 ? 1 : -1;
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    assert(sv->decision_pos == 0 && sv->decision_neg == 0);
    V4("Setting decision %d for var %u\n", val, var_id);
    stack_push_op(s->stack, SKOLEM_OP_DECISION, (void*) (long) var_id);
    if (val > 0) {
        sv->decision_pos = 1;
    } else {
        sv->decision_neg = 1;
    }
}

void skolem_update_dependencies(Skolem* s, unsigned var_id, union Dependencies deps) {
#ifdef DEBUG
    Var* v = var_vector_get(s->qcnf->vars, var_id);
    Scope* scope = vector_get(s->qcnf->scopes, v->scope_id);
    assert(! qcnf_is_DQBF(s->qcnf) || int_vector_includes_sorted(scope->vars, deps.dependencies));
#endif
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    skolem_enlarge_skolem_var_vector(s, var_id);
    if (qcnf_is_DQBF(s->qcnf)) {
        V4("Setting dependencies ");
        assert(int_vector_is_strictly_sorted(deps.dependencies));
        int_vector_print(deps.dependencies);
        V4(" for var %u\n", var_id);
        DEPENDENCECY_UPDATE* du = malloc(sizeof(DEPENDENCECY_UPDATE));
        du->var_id = var_id;
        du->dependencies = sv->dep.dependencies;
        stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_DEPENDENCIES, (void*) du);
    } else {
        if (deps.dependence_lvl != sv->dep.dependence_lvl) {
            V4("Setting dependency level %d for var %u\n", deps.dependence_lvl, var_id);
            union skolem_undo_union suu;
            suu.sus.var_id = var_id;
            suu.sus.val = (int) sv->dep.dependence_lvl;
            stack_push_op(s->stack, SKOLEM_OP_UPDATE_INFO_DEPENDENCIES, suu.ptr);
        }
    }
    sv->dep = deps;
}

void skolem_undo_dependencies(Skolem* s, void* data) {
    union skolem_undo_union suu;
    suu.ptr = data;
    union Dependencies deps;
    if (qcnf_is_DQBF(s->qcnf)) {
        struct DEPENDENCECY_UPDATE* du = (struct DEPENDENCECY_UPDATE*) data;
        deps.dependencies = du->dependencies;
        free(du);
    } else {
        deps.dependence_lvl = (unsigned) suu.sus.val;
    }
    skolem_var* si = skolem_var_vector_get(s->infos, suu.sus.var_id);
    si->dep = deps;
}

bool skolem_is_deterministic(Skolem* s, unsigned var_id) {
    assert(var_id != 0);
    assert(var_id < 100000000); // just a safety measure, if you actually see variables with IDs > 10000000 you are probably screwed.
    skolem_enlarge_skolem_var_vector(s, var_id);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    return sv->deterministic;
}

float skolem_get_conflict_potential(Skolem* s, unsigned var_id) {
    assert(var_id != 0);
    skolem_var sv = skolem_get_info(s, var_id);
    assert(sv.conflict_potential >= 0.0f);
    return sv.conflict_potential + s->magic.conflict_potential_offset;
}
void skolem_bump_conflict_potential(Skolem* s, unsigned var_id) {
    assert(var_id != 0);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    sv->conflict_potential = 1.0f;
    //    sv->conflict_potential = 1.0f - (1.0f - sv->conflict_potential) * s->conflict_potential_change_factor;
}
void skolem_slash_conflict_potential(Skolem* s, unsigned var_id) {
    assert(var_id != 0);
    skolem_var* sv = skolem_var_vector_get(s->infos, var_id);
    sv->conflict_potential *= s->magic.conflict_potential_change_factor;
    assert(sv->conflict_potential >= 0.0f);
}

union Dependencies skolem_get_dependencies(Skolem* s, unsigned var_id) {
    assert((int) var_id > 0); // is not a lit
    skolem_var si = skolem_get_info(s, var_id);
    return si.dep;
}
