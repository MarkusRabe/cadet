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
#include "statistics.h"

struct conflict_analysis;
typedef struct conflict_analysis conflict_analysis;

struct conflict_analysis {
    C2* c2;
    worklist* queue; // literals
    int_vector* conflicting_assignment;
    void* domain;
    int (*domain_get_value)(void* domain, Lit lit);
    bool (*domain_is_relevant_clause)(void* domain, Clause* c, Lit lit);
    bool (*domain_is_legal_dependence)(void* domain, unsigned var_id, unsigned depending_on);
    unsigned (*domain_get_decision_lvl)(void* domain, unsigned var_id);
    
    unsigned conflicted_var_id;
    Clause* conflicted_clause;
    unsigned conflict_decision_lvl;
    
    // Conflict minimization
    PartialAssignment* minimization_pa;
    Stats* minimization_stats;
};

conflict_analysis* conflcit_analysis_init(C2* c2);
void conflict_analysis_free(conflict_analysis* ca);

int_vector* analyze_assignment_conflict(C2* c2,
                                        unsigned conflict_var,
                                        Clause* conflicted_clause,
                                        void* domain,
                                        int  (*domain_get_value)(void* domain, Lit lit),
                                        bool (*domain_is_relevant_clause)(void* domain, Clause* c, Lit lit),
                                        bool (*domain_is_legal_dependence)(void* domain, unsigned var_id, unsigned depending_on),
                                        unsigned (*domain_get_decision_lvl)(void* domain, unsigned var_id));


#endif /* conflict_analysis_h */
