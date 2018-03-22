//
//  debug.h
//  cadet
//
//  Created by Markus Rabe on 21/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef debug_h
#define debug_h

#include "cadet_internal.h"

void debug_fuzz_for_incompleteness(C2* c2, unsigned num_trials);
void debug_print_histogram_of_activities(C2* c2, bool only_deterministic);

#endif /* debug_h */
