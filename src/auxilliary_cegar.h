//
//  auxilliary_cegar.h
//  cadet
//
//  Created by Markus Rabe on 28/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef auxilliary_cegar_h
#define auxilliary_cegar_h

#include "cadet2.h"

#include <stdio.h>
typedef struct Cegar Cegar;
struct Cegar {
    SATSolver* exists_solver;
    QCNF* qcnf;
    int_vector* interface_vars;
    int_vector* is_used_in_lemma;
    int_vector* additional_assignment;
    
    vector* cubes;
    
    // Statistics
    unsigned successful_minimizations;
    unsigned additional_assignments_num;
    unsigned successful_minimizations_by_additional_assignments;
};

/* Initializes a cegar object, including the SAT solver using 
 * the current determinicity information in c2->skolem. 
 */
Cegar* cegar_init(C2*);
void cegar_free(Cegar* c);

/*
 * Assumes the current assignment of the satsolver c2->skolem->skolem 
 * and checks for the existence of an assignment for the nondeterministic 
 * (at the time of creation of the cegar object) existentials satisfying 
 * all constraints.
 */
cadet_res cegar_build_abstraction_for_assignment(C2*);
int cegar_get_val(void* domain, Lit lit);
cadet_res cegar_solve_2QBF(C2* c2);

void cegar_print_statistics(Cegar*);

#endif /* auxilliary_cegar_h */
