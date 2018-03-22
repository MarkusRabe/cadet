//
//  cadet2.h
//  cadet
//
//  Created by Markus Rabe on 15/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef cadet2_h
#define cadet2_h

#include "int_vector.h"
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
cadet_res c2_solve_qdimacs(FILE*, Options*);
C2* c2_from_file(FILE*, Options*);
C2* c2_from_qaiger(aiger*, Options*);
void c2_add_lit(C2*, int);
void c2_new_variable(C2*, bool is_universal, unsigned scope_id, unsigned var_id);
void c2_simplify(C2*);

cadet_res c2_sat(C2*);
cadet_res c2_result(C2*);

int c2_val (C2* c2, int lit);
int_vector* c2_refuting_assignment(C2*);
void c2_print_certificate(C2*);


void c2_print_statistics(C2*);

#endif /* cadet2_h */
