//
//  incremental_determinization.h
//  caqe
//
//  Created by Markus Rabe on 11/12/15.
//  Copyright © 2015 Saarland University. All rights reserved.
//

#ifndef incremental_determinization_h
#define incremental_determinization_h

#include "matrix.h"
#include "satsolver.h"
#include "statistics.h"
#include "options.h"
#include "util.h"

#include <stdio.h>

typedef enum {
    CADET_READY     =  1,
    CADET_CONFLICT  =  2
} cadet_state;

struct CADET {
    Matrix* matrix;
    Options* options;
    SATSolver* skolem;
    vector* skolem_vars;
    
    // Conflict
    MClause* conflict_clause; // stores the last conflict clause
    int_vector* refuting_assignment;
        
    cadet_state state;
    cadet_res result;
    
    size_t decisions;
    
    // Magic constants
    size_t initial_restart;
    size_t next_restart;
    float restart_factor;
    float occurrence_size_weight;
    float conflict_var_weight;
    float conflict_clause_weight;
    float long_clause_death_rate_on_restart_per_literal;
    float decision_var_activity_modifier;
    int small_clause_threshold;
    float decay_rate;
    size_t major_restart_frequency;
    
    // data structures for implicite implication graph traversal
    heap* variables_to_check_for_conflict_analysis;
    map* variables_contained_in_conflict_analysis_heap;
    MVar* conflicted_var;
    map* learnt_clauses_propagation_check_after_backtracking; // Maps learnt clauses to decision levels. When the decision level backtracks behind the indicated level, we want to (re)do the direction test. 
    
    // statistics
    size_t deterministic_vars;
    size_t one_sided_deterministic_vars;
    size_t symbolic_QBCE_deterministic;
    size_t determinicity_sat_calls;
    size_t local_conflict_sat_calls;
    size_t global_conflict_sat_calls;
    size_t conflicts;
    size_t added_clauses;
    size_t restarts;
    
    Stats* decision_conflict_timer;
    Stats* propagation_conflict_timer;
};

typedef struct CADET CADET;

// matrix-dependent interface
int cadet_solve_qdimacs(FILE*, Options*);

// matrix-independent interface
CADET* cadet_init();
cadet_res cadet_solve(CADET*);
void cadet_free(CADET*);
void cadet_new_universal_quantifier(CADET*); // Adds a new innermost universal quantifier.
void cadet_new_existential_quantifier(CADET*); // Adds a new innermost existential quantifier.
void cadet_create_var(CADET*, int var_id); // Adds a new variable with given ID to the innermost quantifier.
MVar* cadet_fresh_var(CADET*); // Creates a fresh variable on the innermost quantifier level.
void cadet_add_lit(CADET*, int); // Adds a new literal to the current clause. The literal 0 closes the current clause and adds it to the matrix. Unclosed clauses are ignored during solving.
void cadet_cancel_current_clause(CADET*);

bool cadet_variable_exists(CADET*, int);
int_vector* cadet_refuting_assignment(CADET*);

int cadet_push(CADET*);
int cadet_pop(CADET*);
void cadet_recover_from_conflict(CADET*);

//void check_for_unique_direction(CADET*, MClause* c);

#endif /* incremental_determinization_h */
