//
//  examples.h
//  cadet
//
//  Created by Markus Rabe on 24/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef examples_h
#define examples_h

#include "partial_assignment.h"
#include "skolem.h"
#include "statistics.h"

struct Examples;
typedef struct Examples Examples;

struct Examples {
    QCNF* qcnf;
    unsigned example_max_num;
//    float_vector* activity; // tracks the recent success/usefulness of each example
    vector* ex; // vector of partial_assignment domains
    PartialAssignment* conflicted_pa;
    unsigned push_count;
    
    // Statistics
    Stats* create_random;
    Stats* create_skolem;
};

Examples* examples_init(QCNF*, unsigned examples_max_num);
void examples_free(Examples*);
void examples_print_statistics(Examples*);

void examples_push(Examples*);
void examples_pop(Examples*);

int examples_get_value_for_conflict_analysis(void*,Lit);
void examples_decision(Examples* e, Lit decision_lit);
PartialAssignment* examples_get_conflicted_assignment(Examples*);
bool examples_is_conflicted(Examples* e);

PartialAssignment* examples_add_assignment_from_skolem(Examples*,Skolem*);
PartialAssignment* examples_add_random_assignment(Examples*);

#endif /* examples_h */
