//
//  partial_assignment.h
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef partial_assignment_h
#define partial_assignment_h

#include "qcnf.h"
#include "heap.h"
#include "undo_stack.h"
#include "val_vector.h"

//#include <stdio.h>

struct PartialAssignment;
typedef struct PartialAssignment PartialAssignment;

// lattice
typedef enum {
    top = 0,
    ff = 1,
    tt = 2,
    bottom = 3 // if not bottom, val-1 gives the value in the sat format // currently bottom is not used
} VAL;

struct PartialAssignment {
    QCNF* qcnf;
    worklist* clauses_to_check; // stores Clause pointers
    val_vector* vals; // an array of VALs indexed by var_id. Length must be consistent with max_var_id of qcnf.
    vector* causes; // mapping var_id to Clause*. Indicates which clause propagated the variable
    
    unsigned decision_lvl;
    int_vector* decision_lvls;
    
    Clause* conflicted_clause;
    unsigned conflicted_var;
    
    Stack* stack;
    
    // Statistics
    size_t assigned_variables;
    size_t conflicts;
    size_t propagations;
};

PartialAssignment* partial_assignment_init(QCNF*);
void partial_assignment_free(PartialAssignment*);

void partial_assignment_pop(PartialAssignment*);
void partial_assignment_push(PartialAssignment*);

void partial_assignment_set_val(PartialAssignment* pa, unsigned var_id, VAL v);
VAL partial_assignment_get_val(PartialAssignment* pa, unsigned var_id);

void partial_assignment_assign_value(PartialAssignment*,Lit);
void partial_assignment_propagate_clause(PartialAssignment*,Clause*); // returns the propagated Lit, or 0 if nothing was propagated

void partial_assignment_go_into_conflict_state(PartialAssignment*, Clause* conflicted_clause, unsigned conflicted_var);

Lit partial_assignment_is_clause_satisfied(PartialAssignment*,Clause*);
bool partial_assignment_is_antecedent_satisfied(PartialAssignment*, Clause*, Lit consequence); // assuming the specified Lit is the consequence, is the antecedent satsified (i.e. all other lits are false)?  

//int compare(VAL,VAL); // -1 is smaller, 0 is equal or incomparable, 1 is greater

// INTERACTION WITH CADET2
void partial_assignment_propagate(PartialAssignment* pa);
bool partial_assignment_is_conflicted(PartialAssignment*);
void partial_assignment_new_clause(PartialAssignment* pa, Clause* c);

// INTERACTION WITH CONFLICT ANALYSIS
bool partial_assignment_is_legal_dependence(void* s, unsigned var_id, unsigned depending_on);
int partial_assignment_get_value_for_conflict_analysis(void* domain, Lit lit);
bool partial_assignment_is_relevant_clause(void* domain, Clause* c, Lit lit);
Clause* partial_assignment_get_relevant_clause(void* domain, unsigned var_id);
unsigned partial_assignment_get_decision_lvl(void* domain, unsigned var_id);


// PRINTING
void pa_print_debug_info(PartialAssignment*);
void partial_assignment_print_statistics(PartialAssignment*);

// PRIVATE FUNCTIONS
typedef enum {
    PA_OP_ASSIGN,
    PA_OP_CONFLICT,
    PA_OP_DLVL
} PA_OPERATION;

void partial_assignment_undo(void* pa,char,void*);

#endif /* partial_assignment_h */
