//
//  c2_cegar.h
//  cadet
//
//  Created by Markus Rabe on 28/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef c2_cegar_h
#define c2_cegar_h

#include "cadet2.h"
#include "satsolver.h"

#include <stdio.h>
typedef struct Cegar Cegar;
struct Cegar {
    SATSolver* exists_solver;
    Skolem* skolem;
    int_vector* interface_vars;
    int_vector* is_used_in_lemma;
    int_vector* additional_assignment;
    
    vector* solved_cubes;
    
    // Magic values
    unsigned cegar_effectiveness_threshold;
    
    // Statistics
    unsigned successful_minimizations;
    unsigned additional_assignments_num;
    unsigned successful_minimizations_by_additional_assignments;
    unsigned cubes_num;
    float recent_average_cube_size;
};

/* Initializes a cegar object, including the SAT solver using 
 * the current determinicity information in c2->skolem. 
 */
Cegar* cegar_init(Skolem*);
void cegar_free(Cegar* c);

/*
 * Assumes the current assignment of the satsolver c2->skolem->skolem 
 * and checks for the existence of an assignment for the nondeterministic 
 * (at the time of creation of the cegar object) existentials satisfying 
 * all constraints.
 * 
 * May change the state of C2 when termination criterion is found.
 */
cadet_res cegar_build_abstraction_for_assignment(C2*);
int cegar_get_val(void* domain, Lit lit, bool second_copy);
cadet_res cegar_solve_2QBF(C2* c2, int rounds_num);
void cegar_do_cegar_if_effective(C2* c2);
bool cegar_try_to_handle_conflict(Cegar*);
void cegar_print_statistics(Cegar*);
void cegar_update_interface(Cegar*);
bool cegar_is_initialized(Cegar*);
void cegar_new_cube(Cegar*, int_vector*);

#endif /* c2_cegar_h */
