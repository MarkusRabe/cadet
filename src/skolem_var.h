//
//  skolem_var.h
//  cadet
//
//  Created by Markus Rabe on 27/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef skolem_var_h
#define skolem_var_h

#include "int_vector.h"
#include "skolem_dependencies.h"

struct Skolem;
typedef struct Skolem Skolem;
struct skolem_var;
typedef struct skolem_var skolem_var;

union Dependencies;

struct skolem_undo_struct {
    unsigned var_id;
    int val;
};
union skolem_undo_union {
    struct skolem_undo_struct sus;
    void* ptr;
};

struct skolem_var {
    // undoable portion of skolem_vars
    int pos_lit; // refers to lit in skolem satsolver; 0 value denotes that the lit is constant FALSE; s->satlit_true denotes that the lit is constant TRUE
    int neg_lit : 27; // refers to lit in skolem satsolver; 0 value denotes that the lit is constant FALSE; s->satlit_true denotes that the lit is constant TRUE
    unsigned pure_pos : 1;
    unsigned pure_neg : 1;
    unsigned deterministic : 1;
    unsigned decision_pos : 1;
    unsigned decision_neg : 1;
    
    int depends_on_decision_satlit;
    
    union Dependencies dep; // depends on whether we consider a QBF or a DQBF
    
    // permanent portion of skolem_var
    float conflict_potential;
    unsigned decision_lvl;
    unsigned reason_for_constant;
    unsigned dlvl_for_constant;
};

bool skolem_is_deterministic(Skolem*, unsigned var_id);
void skolem_enlarge_skolem_var_vector(Skolem*, unsigned var_id);
skolem_var skolem_get_info(Skolem*, unsigned var_id);
void skolem_update_pos_lit(Skolem*, unsigned var_id, int pos_lit);
void skolem_update_neg_lit(Skolem*, unsigned var_id, int pos_lit);
void skolem_update_satlit(Skolem* s, Lit lit, int new_satlit);
void skolem_update_pure_pos(Skolem*, unsigned var_id, unsigned pos_lit);
void skolem_update_pure_neg(Skolem*, unsigned var_id, unsigned pos_lit);
void skolem_update_deterministic(Skolem*, unsigned var_id);
void skolem_update_decision(Skolem*, Lit lit);
void skolem_update_dependencies(Skolem*, unsigned var_id, union Dependencies deps);
void skolem_undo_dependencies(Skolem*, void* data);

unsigned skolem_get_decision_lvl_for_conflict_analysis(void*, unsigned var_id);
unsigned skolem_get_decision_lvl(Skolem*, unsigned var_id);
unsigned skolem_is_decision_var(Skolem*, unsigned var_id);
int skolem_get_decision_val(Skolem*, unsigned var_id);
int skolem_get_pure_val(Skolem*, unsigned var_id);
void skolem_update_decision_lvl(Skolem*, unsigned var_id, unsigned dlvl);
void skolem_undo_decision_lvl(Skolem*, void* data);

unsigned skolem_get_reason_for_constant(Skolem*, unsigned var_id);
unsigned skolem_get_dlvl_for_constant(Skolem*, unsigned var_id);
void skolem_update_reason_for_constant(Skolem*, unsigned var_id, unsigned clause_id, unsigned dlvl);
void skolem_undo_reason_for_constant(Skolem*, void* data);


union Dependencies skolem_get_dependencies(Skolem*, unsigned);

float skolem_get_conflict_potential(Skolem*, unsigned var_id);
void skolem_bump_conflict_potential(Skolem*, unsigned var_id);
void skolem_slash_conflict_potential(Skolem*, unsigned var_id);

void skolem_print_skolem_var(Skolem*, skolem_var* si, unsigned indent);

#endif /* skolem_var_h */
