//
//  cadet2.h
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef cadet2_h
#define cadet2_h

#include "skolem.h"
#include "qcnf.h"
#include "options.h"
#include "examples.h"
#include "val_vector.h"

#include <stdio.h>

struct C2;
typedef struct C2 C2;

typedef enum {
    C2_READY,
    C2_PA_CONFLICT,
    C2_SKOLEM_CONFLICT,
    C2_CEGAR_CONFLICT,
    C2_EMPTY_CLAUSE_CONFLICT,
    C2_PROPOSITIONAL_CONFLICT,
    C2_EXAMPLES_CONFLICT
} c2_state;

typedef enum {
    C2_CASE_SPLIT_DEPTH_PENALTY_EXPONENTIAL,
    C2_CASE_SPLIT_DEPTH_PENALTY_QUADRATIC
} C2_CSDP;

struct C2_Statistics {
    size_t conflicts;
    size_t added_clauses;
    size_t decisions;
    size_t successful_conflict_clause_minimizations;
    size_t cases_explored;
    size_t lvls_backtracked;
    
    double start_time;
    
    Stats* failed_literals_stats;
    size_t failed_literals_conflicts;
};

struct C2_Magic_Values {
    unsigned initial_restart;
    float restart_factor;
    float conflict_var_weight;
    float conflict_clause_weight;
    float long_clause_death_rate_on_restart_per_literal;
    float decision_var_activity_modifier;
    float implication_graph_variable_activity;
    float decay_rate;
    size_t major_restart_frequency;
    unsigned num_restarts_before_Jeroslow_Wang;
    
    // Magic constants for case splits
    unsigned num_restarts_before_case_splits;
    float skolem_success_horizon; // for case splits (factor describing how the receding horizon is built)
    float notoriousity_threshold_factor; // for case splits
    float skolem_success_recent_average_initialization;
};

struct C2 {
    QCNF* qcnf;
    Options* options;

    // Essential C2 data structures
    val_vector* decision_vals; // indexed by var_id
    c2_state state;
    cadet_res result;
    size_t restarts;
    unsigned next_restart;
    unsigned restart_base_decision_lvl; // decision_lvl used for restarts
    Stack* stack; // for backtracking
    
    // Reasoning domains
    Skolem* skolem;
    Examples* examples;
    
    // Data structures for heuristics
    float activity_factor;
    
    // Case splits
    int_vector* case_split_stack;
    size_t decisions_since_last_conflict;
    float skolem_success_recent_average;
    C2_CSDP case_split_depth_penalty;
    size_t conflicts_between_case_splits;
    size_t conflicts_between_case_splits_countdown;
    
    struct C2_Statistics statistics;
    
    struct C2_Magic_Values magic;
};

C2* c2_init(Options* options);
C2* c2_init_qcnf(QCNF*, Options* options);
void c2_free(C2* c2);

// Push and pop are for external use. 
void c2_push(C2*);
void c2_pop(C2*);
Clause* c2_add_lit(C2* c2, Lit lit);
void c2_new_variable(C2* c2, unsigned var_id);
void c2_new_clause(C2* c2, Clause* c);

cadet_res c2_sat(C2*);
cadet_res c2_solve_qdimacs(FILE*,Options*);
cadet_res c2_solve(C2* c2);

// PRINTING
void c2_print_statistics(C2*);
void c2_print_debug_info(C2*);

// PRIVATE FUNCTIONS
typedef enum {
    C2_OP_ASSIGN_DECISION_VAL
} C2_OPERATION;
void c2_undo(void* parent, char type, void* obj);

float c2_get_activity(C2* c2, unsigned var_id);
void c2_set_activity(C2* c2, unsigned var_id, float val);
void c2_increase_activity(C2* c2, unsigned var_id, float summand);
void c2_scale_activity(C2* c2, unsigned var_id, float factor);
unsigned c2_get_decision_lvl(C2* c2, unsigned var_id);
void c2_backtrack_to_decision_lvl(C2 *c2, unsigned backtracking_lvl);

bool c2_is_decision_var(C2*, unsigned var_id);
int c2_get_decision_val(C2*, unsigned var_id);

// figuring out properties of instances:
void c2_analysis_determine_number_of_partitions(C2* c2);

#endif /* cadet2_h */
