//
//  skolem.h
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef skolem_h
#define skolem_h

#include "qcnf.h"
#include "heap.h"
#include "undo_stack.h"
#include "function.h"
#include "partial_assignment.h"
#include "util.h"
#include "pqueue.h"
#include "skolem_var_vector.h"
#include "skolem_dependencies.h"
#include "skolem_var.h"
#include "skolem_constants.h"
#include "options.h"
#include "statistics.h"

#include <stdio.h>

struct Skolem;
typedef struct Skolem Skolem;
struct skolem_var;
typedef struct skolem_var skolem_var;
struct Cegar;
typedef struct Cegar Cegar;

bool skolem_is_total(skolem_var*); // pos_lit == neg_lit && pos_lit != 0
bool skolem_is_top(skolem_var*); // pos_lit == 0 && neg_lit == 0

typedef enum {
    SKOLEM_MODE_STANDARD, // propagate determinicity and check for conflicts
    SKOLEM_MODE_CONSTANT_PROPAGATIONS_TO_DETERMINISTICS, // used for assumptions
    SKOLEM_MODE_RECORD_POTENTIAL_CONFLICTS
} SKOLEM_MODE;

typedef enum {
    SKOLEM_STATE_READY,
    SKOLEM_STATE_SKOLEM_CONFLICT,
    SKOLEM_STATE_CONSTANTS_CONLICT,
    SKOLEM_STATE_BACKPROPAGATION_CONFLICT
} SKOLEM_STATE;

struct Skolem_Statistics {
    // Statistics
    size_t propagations;
    size_t pure_vars;
    size_t pure_constants;
    size_t local_determinicity_checks;
    size_t local_conflict_checks;
    size_t global_conflict_checks;
    
    size_t backpropagation_sat_checks;
    size_t backpropagations;
    size_t backpropagation_conflicts;

    size_t explicit_propagations;
    size_t explicit_propagation_conflicts;
    
    size_t decisions;
    
    Stats* global_conflict_checks_sat;
    Stats* global_conflict_checks_unsat;
};

struct Skolem_Magic_Values {
    // Magic constants
    float initial_conflict_potential;
    float conflict_potential_change_factor;
    float conflict_potential_threshold;
    float conflict_potential_offset;
    unsigned blocked_clause_occurrence_cutoff;
};

struct Skolem {
    // Links to objects outside of Skolem domain
    Options* options;
    QCNF* qcnf;
    
    // Dependent objects
    Function* f;
    
    // Core Skolem state and data structures
    unsigned decision_lvl;
    SKOLEM_STATE state;
    unsigned conflict_var_id; // only assigned in case of conflict
    Clause* conflicted_clause; // only assigned in case of conflict
    // All information about the variables that is relevant to the Skolem domain
    skolem_var_vector* infos; // contains skolem_var; indexed by var_id
    // All information Skolem domain needs about clauses: the unique consequences for all clauses
    int_vector* unique_consequence; // contains lit indexed by clause_id
    
    // Extra data structure required for functional synthesis
    vector* decision_indicator_sat_lits; // contains var_id of temporary vars
    
    /* Propagation worklists:
     * Constants are propagated through the clauses_to_check worklist.
     * For determinicity propagation, variables are first added to determinicity_queue,
     * if they are not deterministic, they are added to pure_var_queue to later check 
     * if they are pure.
     */
    worklist* clauses_to_check; // stores Clause*; this worklist is used for both clauses that might propagate constants, and also for backpropagation checks. Its a bit weird
    pqueue* determinicity_queue; // contains unsigned var_id
    pqueue* pure_var_queue; // contains unsigned var_id
        
    // Configuration
    SKOLEM_MODE mode; // can be used to switch of all or certain types of conflicts
    unsigned u_initially_deterministic; // what should be considered deterministic?
    unsigned e_initially_deterministic; // what should be considered deterministic?
    
    
    // THE empty_dependency object
    // Used when non-existent skolem_vars should return a dependency set; avoids alloc/free management
    union Dependencies empty_dependencies;
    
    // Keeping track of progress; not essential currently
    size_t deterministic_variables;
    
    // Backtracking
    Stack* stack;
    
    struct Skolem_Statistics statistics;
    
    struct Skolem_Magic_Values magic;
};

Skolem* skolem_init(QCNF*,Options*, unsigned u_initially_deterministic, unsigned e_initially_deterministic);
void skolem_free(Skolem*);

// INTERACTION WITH CONFLICT ANALYSIS
bool skolem_is_legal_dependence_for_conflict_analysis(void* s, unsigned var_id, unsigned depending_on);
int skolem_get_value_for_conflict_analysis(void* domain, Lit lit, bool second_copy);
Clause* skolem_get_reason_for_conflict_analysis(void* skolem, Lit lit, bool second_copy);

// INTERACTION WITH CADET2
void skolem_new_clause(Skolem*,Clause*);
void skolem_assign_constant_value(Skolem*,Lit,union Dependencies, Clause* reason); // reason may be NULL
void skolem_assume_constant_value(Skolem*,Lit);
int skolem_get_constant_value(Skolem*, Lit);
bool skolem_is_initially_deterministic(Skolem* s, unsigned var_id);

bool skolem_can_propagate(Skolem*);
void skolem_propagate(Skolem*);
void skolem_decision(Skolem*, Lit lit);

void skolem_push(Skolem*);
void skolem_pop(Skolem*);
void skolem_recover_from_conflict(Skolem*);

void skolem_increase_decision_lvl(Skolem*);

unsigned skolem_global_conflict_check(Skolem*, unsigned var_id);
bool skolem_is_conflicted(Skolem*);




// PRINTING
void skolem_print_debug_info(Skolem*);
void skolem_print_statistics(Skolem*);

// PRIVATE FUNCTIONS

typedef enum {
    SKOLEM_OP_UPDATE_INFO_POS_LIT, // obj contains the variable and the previous poslit, see union skolem_undo_union
    SKOLEM_OP_UPDATE_INFO_NEG_LIT, // obj contains the variable and the previous neglit, see union skolem_undo_union
    SKOLEM_OP_UPDATE_INFO_DETERMINISTIC, // obj contains the variable and a single bit, see union skolem_undo_union
    SKOLEM_OP_UPDATE_INFO_PURE_POS, // obj contains the variable and a single bit, see union skolem_undo_union
    SKOLEM_OP_UPDATE_INFO_PURE_NEG, // obj contains the variable and a single bit, see union skolem_undo_union
    SKOLEM_OP_UPDATE_INFO_DEPENDENCIES, // depending on mode, obj contains the variable and previous dependency level, or a pointer to a Dependency_Update_struct
    SKOLEM_OP_UPDATE_INFO_DECISION_LVL,
    SKOLEM_OP_UPDATE_INFO_REASON_FOR_CONSTANT,
    SKOLEM_OP_UNIQUE_CONSEQUENCE,
    SKOLEM_OP_DECISION
} SKOLEM_OP;

void skolem_undo(void*,char,void*);
void skolem_update_clause_worklist(Skolem* s, int unassigned_lit);
void skolem_propagate_determinicity_over_clause(Skolem*,QCNF*,Clause*);
void skolem_propagate_explicit_assignments(Skolem* s);

void skolem_check_occs_for_unique_consequences(Skolem*, Lit lit);
void skolem_check_for_unique_consequence(Skolem*, Clause*);
void skolem_set_unique_consequence(Skolem*, Clause*, Lit);
Lit skolem_get_unique_consequence(Skolem*, Clause*);
bool skolem_has_unique_consequence(Skolem*, Clause*);
bool skolem_is_locally_conflicted(Skolem*, unsigned var_id);

// used by debug.c
satlit skolem_get_satlit(Skolem* s, Lit lit);

#endif /* skolem_h */
