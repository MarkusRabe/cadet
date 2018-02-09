//
//  domain.h
//  cadet
//
//  Created by Markus Rabe on 28/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef domain_h
#define domain_h

#include "cadet2.h"
#include "float_vector.h"

#include <stdio.h>

struct Cegar_Magic_Values {
    unsigned max_cegar_iterations_per_learnt_clause;
    unsigned cegar_effectiveness_threshold;
    float universal_activity_decay;
};

struct Cegar_Statistics {
    unsigned successful_minimizations;
    unsigned additional_assignments_num;
    unsigned successful_minimizations_by_additional_assignments;
    float recent_average_cube_size;
};

struct PartialFunction {
    int_vector* cube; // optional: cube in which this partial function is valid.
    // In certifying mode, one of the following must be assigned
    int_vector* assignment; // assignment to dlvl>0 vars
    QCNF* function; // formula over dlvl>0 vars
};
typedef struct PartialFunction PartialFunction;

typedef struct Domain Domain;
struct Domain {
    QCNF* qcnf;
    
    // dlvl0 interface
    int_vector* interface_vars;
    float_vector* interface_activities; // contains the frequencies of the interface variabes as floats
    map* original_satlits;
    
    vector* solved_cases; // over struct Case*
    
    // CEGAR
    SATSolver* exists_solver; // using original names, no redirect as in the skolem solver
    int_vector* is_used_in_lemma;
    int_vector* additional_assignment;
    struct Cegar_Statistics cegar_stats;
    struct Cegar_Magic_Values cegar_magic;
};

/* Initializes a cegar object, including the SAT solver using 
 * the current determinicity information in c2->skolem. 
 */
Domain* domain_init(QCNF*);
void domain_free(Domain* c);

void domain_completed_case(Skolem* s, int_vector* cube, int_vector* partial_assignment, QCNF* function); // cube is over dlvl0, partial_assignment is over dlvl>0, function is over dlvl>0
void domain_print_statistics(Domain*);
bool domain_is_initialized(Domain*);

// Interface
void domain_update_interface(Skolem*);
float domain_get_interface_activity(Domain*, unsigned var_id);
void domain_add_interface_activity(Domain*, unsigned var_id, float value);
void domain_decay_interface_activity(Domain*, unsigned var_id);

// CEGAR
/*
 * Assumes the current assignment of the satsolver c2->skolem->skolem 
 * and checks for the existence of an assignment for the nondeterministic 
 * (at the time of creation of the cegar object) existentials satisfying 
 * all constraints.
 * 
 * May change the state of C2 when termination criterion is found.
 */
cadet_res domain_do_cegar_for_conflicting_assignment(C2*);
int domain_get_cegar_val(void* domain, Lit lit);
cadet_res domain_solve_2QBF_by_cegar(C2* c2, int rounds_num);
void do_cegar_if_effective(C2* c2);

#endif /* domain_h */
