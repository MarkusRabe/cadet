//
//  function_private.h
//  cadet
//
//  This header is included only by function.c and skolem_function_encoding.c
//
//  Created by Markus Rabe on 12.07.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef function_private_h
#define function_private_h

#include "satsolver.h"

struct Function {
    QCNF* qcnf;
    SATSolver* sat;
    
    // Holds all literals for the clause that is currently being created.
    vector* new_clause;
    
    // Helper variables in the SAT solver
    int satlit_true;
    int_vector* consistency_literals;
};

#endif /* function_private_h */
