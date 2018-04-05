//
//  casesplits.h
//  cadet
//
//  Created by Markus Rabe on 25/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef casesplits_h
#define casesplits_h

#include "float_vector.h"
#include "set.h"
#include "int_vector.h"
#include "qcnf.h"
#include "skolem.h"


#include <stdio.h>

struct Cegar_Magic_Values {
    unsigned max_cegar_iterations_per_learnt_clause;
    unsigned cegar_effectiveness_threshold;
    float universal_activity_decay;
};

struct Cegar_Statistics {
    unsigned successful_minimizations;
    unsigned additional_assignments_num;
    unsigned successful_minimizations_by_additional_assignments;
    float recent_average_cube_size;
};

typedef struct Case Case;
typedef struct Casesplits Casesplits;

struct Case {
    int_vector* universal_assumptions;
    int_vector* determinization_order; // can be an assignment to dlvl>0 vars (for CEGAR) or decisions to be fed to skolem
    int_vector* unique_consequences;
    int_vector* potentially_conflicted_variables;
    char type; // 0 indicates cegar round, 1 indicates case split
    // type listed last, as this reduces memory footprint of this struct by 7 bytes.
};

struct Casesplits {
    Skolem* skolem;
    
    // dlvl0 interface
    int_vector* interface_vars;
    float_vector* interface_activities; // contains the frequencies of the interface variabes as floats
    map* original_satlits;
    
    vector* closed_cases; // over struct Case*
    
    // CEGAR
    SATSolver* exists_solver; // using original names, no redirect as in the skolem solver
    int_vector* is_used_in_lemma;
    int_vector* additional_assignment;
    struct Cegar_Statistics cegar_stats;
    struct Cegar_Magic_Values cegar_magic;
    
    // Statistics
    unsigned case_generalizations;
};

/* Initializes a cegar object, including the SAT solver using
 * the current determinicity information in c2->skolem.
 */
Casesplits* casesplits_init(QCNF*);
bool casesplits_is_initialized(Casesplits*);
void casesplits_free(Casesplits*);

int_vector* case_splits_determinization_order_with_polarities(Skolem*);
void casesplits_encode_closed_case(Casesplits* cs, int_vector* determinization_order, int_vector* universal_assumptions);
void casesplits_encode_CEGAR_case(Casesplits*);
void casesplits_steal_cases(Casesplits* new_cs, Casesplits* old_cs); // for satsolver refreshs
void casesplits_record_cegar_cube(Casesplits*, int_vector* cube, int_vector* partial_assignment);
void casesplits_encode_case_into_satsolver(Skolem*, Case* c, SATSolver* sat);
void casesplits_print_statistics(Casesplits*);

void casesplits_record_conflicts(Skolem* s, int_vector* decision_sequence);
int_vector* casesplits_test_assumptions(Casesplits* cs, int_vector* universal_assumptions);

// Interface
void casesplits_update_interface(Casesplits*,Skolem*);
float casesplits_get_interface_activity(Casesplits*, unsigned var_id);
void casesplits_add_interface_activity(Casesplits*, unsigned var_id, float value);
void casesplits_decay_interface_activity(Casesplits*, unsigned var_id);

#endif /* c2_casesplits_h */
