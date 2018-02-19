//
//  casesplits.h
//  cadet
//
//  Created by Markus Rabe on 25/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef c2_casesplits_h
#define c2_casesplits_h

#include "cadet2.h"

void casesplits_backtrack_case_split(C2* c2);
bool casesplits_assume_single_lit(C2* c2); // returns if any kind of progress happened
void casesplits_close_case(C2* c2);
void casesplits_undo_assumption(C2* c2, void* obj);

#endif /* c2_casesplits_h */
