//
//  c2_traces.h
//  cadet
//
//  Created by Markus Rabe on 25/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef c2_traces_h
#define c2_traces_h

#include "cadet_internal.h"
#include <stdio.h>

void c2_print_variable_states(C2*);
char* c2_literal_color(C2*, Clause*, Lit);
void c2_print_statistics(C2*);
void c2_print_learnt_clause_color_legend();

void c2_log_clause(C2*, Clause*);

void c2_trace_for_profiling_initialize(Options*, SATSolver*);
void c2_trace_for_profiling(C2*);

void c2_print_universals_assignment(C2* c2); // WARNING: Calling this function may change the state of the sat solver!
void c2_print_debug_info(C2* c2);

#endif /* cadet2_outputs_h */
