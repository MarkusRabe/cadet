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
    unsigned alt : 1;
    unsigned var_id : 31;
    int val;
};
union skolem_undo_union {
    struct skolem_undo_struct sus;
    void* ptr;
};

// The satlit contains two integers that are literals in the skolem satsolver. Each integer stands for one copy of the function.
typedef struct satlit { int x[2]; } satlit;

satlit satlit_negate(satlit x);

struct skolem_var {
    // Undoable portion of skolem_vars
    
    // The Skolem function
    // TODO: don't set these fields to 0 initially, but to -f_get_true(s->f)
    // The fields ***_lit indicate the satlits corresponding to the case that the variable has
    // to be positive and that it has to be negative. That is, this is a representation of partial functions.
    // The fields are arrays, containing two values to represent two copies of the skolem functions.
    // The fields are initialized with the value 0, representing that the lit is constant FALSE; s->satlit_true denotes that the lit is constant TRUE
    satlit pos_lit;
    satlit neg_lit;
    
    union Dependencies dep; // depends on whether we consider a QBF or a DQBF
    
    // Permanent portion of skolem_var
    float conflict_potential; // currently not really used
    unsigned reason_for_constant;
    unsigned decision_lvl; // for determinicity
    unsigned dlvl_for_constant : 29; // is a bit shorter to accomodate the bitflags
    
    // Flags:
    unsigned pure_pos : 1;
    unsigned pure_neg : 1;
    unsigned deterministic : 1;
};

bool skolem_is_deterministic(Skolem*, unsigned var_id);
void skolem_enlarge_skolem_var_vector(Skolem*, unsigned var_id);
skolem_var skolem_get_info(Skolem*, unsigned var_id);
void skolem_update_satlit(Skolem* s, Lit lit, satlit new_satlit);
void skolem_update_pure_pos(Skolem*, unsigned var_id, unsigned pos_lit);
void skolem_update_pure_neg(Skolem*, unsigned var_id, unsigned pos_lit);
void skolem_update_deterministic(Skolem*, unsigned var_id, unsigned deterministic);
void skolem_update_dependencies(Skolem*, unsigned var_id, union Dependencies deps);
void skolem_undo_dependencies(Skolem*, void* data);

unsigned skolem_get_decision_lvl_for_conflict_analysis(void*, unsigned var_id);
unsigned skolem_get_decision_lvl(Skolem*, unsigned var_id);
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
