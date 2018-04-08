//
//  cadet2.h
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef cadet2_h
#define cadet2_h

#include "options.h"
#include "aiger.h"

#include <stdio.h>

struct C2;
typedef struct C2 C2;

typedef enum {
    CADET_RESULT_SAT      = 10,
    CADET_RESULT_UNSAT    = 20,
    CADET_RESULT_UNKNOWN  = 30
} cadet_res;


C2* c2_init(Options* options);
void c2_free(C2*);

C2* c2_from_file(FILE*, Options*);
C2* c2_from_qaiger(aiger*, Options*);

// Introduces a new variable with identifier var_id.
void c2_new_2QBF_variable(C2*, bool is_universal, unsigned var_id);
unsigned c2_fresh_variable(C2*, bool is_universal);

// Add new clauses (constraints) by the following command.
// Negative numbers indicate negated variables.
// '0' indicates end of clause.
// Variables used here must be introduced through c2_new_2QBF_variable first.
void c2_add_lit(C2*, int literal);

// Assume the value of a variable.
//  - assuming universals makes formulas easier to solve; after SAT results use c2_is_core to check if necessary
//  - assuming existentials makes formulas harder to solve; after UNSAT results use c2_is_core to check if necessary
// c2_is_core only works when clause minimization is switched off.
void c2_assume(C2*, int literal);
bool c2_is_core(C2*, int assumed_literal);

// Solves the formula encoded in the solver and returns the result.
cadet_res c2_sat(C2*);

// Returns the result of the last solver call, and CADET_RESULT_UNKNOWN if not solved yet.
cadet_res c2_result(C2*);

// Returns the value of the literal of a universal variable; only available after CADET_RESULT_UNSAT result.
int c2_val (C2*, int literal);

// Prints the AIG certificate to the specified file.
void c2_write_AIG_certificate(C2*);

// Print solver statistics on stdout.
void c2_print_statistics(C2*);

// Reads from stdin if file_name is NULL and from specified file otherwise.
// Then solves the problem and prints output. 
cadet_res c2_solve_qdimacs(const char* filename, Options*);

aiger* c2_qaiger_quantifier_elimination(aiger*, char* filename, Options*); // not yet implemented

#endif /* cadet2_h */
