//
//  c2_rl.h
//  cadet
//
//  All functions related to reinforcement learning
//
//  Created by Markus Rabe on 24.01.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#ifndef c2_rl_h
#define c2_rl_h

#include "cadet_internal.h"

void c2_rl_print_state(C2*, unsigned conflicts_until_next_restart, float max_activity);
void c2_rl_print_decision(unsigned decision_var_id, int phase);
void c2_rl_update_constant_value(unsigned var_id, int val); // val indicates if the variable is assigned a constant
void c2_rl_update_unique_consequence(unsigned clause_idx, Lit lit);
void c2_rl_update_D(unsigned var_id, bool deterministic); // Update the member of of var_id in D. True for adding, False for removing
void c2_rl_new_clause(Clause*);
void c2_rl_delete_clause(Clause*);
void c2_rl_conflict(unsigned var_id);
void c2_rl_print_activity(unsigned var_id, float activity);
int c2_rl_get_decision(C2*, unsigned default_decision, float max_activity);

void rl_mute();
void rl_unmute();

int_vector* c2_rl_necessary_learnt_clauses(C2*);
cadet_res c2_rl_run_c2(Options*);
void rl_mock_file(char*);

#endif /* c2_rl_h */
