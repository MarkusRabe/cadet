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
bool c2_case_split(C2* c2); // returns if any kind of progress happened
bool c2_case_splits_make_assumption(C2* c2, Lit lit);
void c2_close_case(C2* c2);
void c2_case_splits_undo_assumption(C2* c2, void* obj);

#endif /* c2_casesplits_h */
