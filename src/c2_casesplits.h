//
//  c2_casesplits.h
//  cadet
//
//  Created by Markus Rabe on 25/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef c2_casesplits_h
#define c2_casesplits_h

#include "cadet2.h"

void c2_backtrack_case_split(C2* c2);
void c2_case_split_backtracking_heuristics(C2* c2);
bool c2_case_split(C2* c2); // returns if any kind of progress happened
float c2_notoriousity(C2* c2, Lit lit);
float c2_notoriousity_threshold(C2* c2);

int c2_pick_most_notorious_literal(C2* c2);

int_vector* c2_determine_notorious_determinsitic_variables(C2* c2);

#endif /* c2_casesplits_h */
