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

#include "cadet2.h"
#include <stdio.h>

void c2_rl_print_state(C2* c2, unsigned conflicts_until_next_restart, unsigned decision_var_id, int phase);
void c2_rl_update_D(Options* o, unsigned var_id, bool deterministic); // Update the member of of var_id in D. True for adding, False for removing.
void c2_rl_learnt_clause(Options* o, Clause* c);
void c2_rl_print_activity(Options* o, unsigned var_id, float activity);
int c2_rl_get_decision();

#endif /* c2_rl_h */
