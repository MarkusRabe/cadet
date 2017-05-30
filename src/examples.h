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
#include "undo_stack.h"

struct Examples;
typedef struct Examples Examples;

typedef enum {
    EXAMPLES_STATE_READY,
    EXAMPLES_STATE_INCONSISTENT_DECISION_CONFLICT,
    EXAMPLES_STATE_PROPAGATION_CONFLICT
} EXAMPLES_STATE;

struct Examples {
    QCNF* qcnf;
    unsigned example_max_num;
//    float_vector* activity; // tracks the recent success/usefulness of each example
    vector* ex; // vector of partial_assignment domains
    PartialAssignment* conflicted_pa;
    
    EXAMPLES_STATE state;
    
    Stack* stack;
    
    // Statistics
    Stats* create_random;
    Stats* create_skolem;
};

Examples* examples_init(QCNF*, unsigned examples_max_num);
void examples_free(Examples*);
void examples_print_statistics(Examples*);

void examples_push(Examples*);
void examples_pop(Examples*);
void examples_undo(void*,char,void*); // for internal use only
void examples_redo(Examples*, Skolem*, PartialAssignment* pa);

void examples_new_clause(Examples*, Clause*);
void examples_propagate(Examples*);

int examples_get_value_for_conflict_analysis(void*,Lit);
bool examples_is_decision_consistent_with_skolem(Examples*, Skolem*, Lit decision_lit);
void examples_decision(Examples*, Lit decision_lit);
void examples_decision_consistent_with_skolem(Examples*, Skolem*, Lit decision_lit);
PartialAssignment* examples_get_conflicted_assignment(Examples*);
bool examples_is_conflicted(Examples*);

PartialAssignment* examples_add_assignment_from_skolem(Examples*,Skolem*);
PartialAssignment* examples_add_random_assignment(Examples*);

#endif /* examples_h */
