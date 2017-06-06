//
//  conflict_analysis.h
//  cadet
//
//  Created by Markus Rabe on 25/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef conflict_analysis_h
#define conflict_analysis_h

#include "cadet2.h"

int_vector* analyze_assignment_conflict(C2* c2,
                                        unsigned conflict_var,
                                        Clause* conflicted_clause,
                                        void* domain,
                                        int  (*domain_get_value)(void* domain, Lit lit),
                                        Clause* (*domain_get_reason)(void* domain, Lit lit),
                                        bool (*domain_is_legal_dependence)(void* domain, unsigned var_id, unsigned depending_on),
                                        unsigned (*domain_get_decision_lvl)(void* domain, unsigned var_id));


#endif /* conflict_analysis_h */
