//
//  skolem_dependencies.h
//  cadet
//
//  Created by Markus Rabe on 09/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef skolem_dependencies_h
#define skolem_dependencies_h

#include "int_vector.h"
#include "qcnf.h"

struct Skolem;
typedef struct Skolem Skolem;

union Dependencies { // dependencies have different representations when we consider QBFs and DQBFs
    int_vector* dependencies; // explicit list of variable IDs of universal varialbes
    unsigned dependence_lvl; // quantifier level, starting with 0 for the propositional level
};

typedef enum {
    DEPS_EQUAL = 0,
    DEPS_SMALLER = 1,
    DEPS_LARGER = 2,
    DEPS_INCOMPARABLE = 3,
} DEPENDENCY_COMPARISON;

bool skolem_has_illegal_dependence(Skolem* s, Clause* c);
bool skolem_occs_contain_illegal_dependence(Skolem* s, Lit lit);
bool skolem_is_legal_dependency(Skolem* s, unsigned var_id, union Dependencies);
bool skolem_may_depend_on(Skolem* s, unsigned var_id, unsigned depending_on);

union Dependencies skolem_compute_dependencies(Skolem* s, unsigned var_id);
void skolem_update_dependencies_for_lit(Skolem* s, union Dependencies* aggregate_dependencies, Lit lit);

union Dependencies skolem_create_fresh_empty_dep(Skolem* s);
DEPENDENCY_COMPARISON skolem_compare_dependencies(Skolem* s, union Dependencies deps1, union Dependencies deps2);
union Dependencies skolem_copy_dependencies(Skolem* s, union Dependencies deps);
void skolem_free_dependencies(Skolem* s, union Dependencies deps);

#endif /* skolem_dependencies_h */
