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
    union {
        struct { // for completed cegar rounds
            int_vector* cube; // optional: cube in which this partial function is valid.
            int_vector* assignment; // assignment to dlvl>0 vars
        } ass;
        struct { // for completed case split
            int_vector* decisions;
            set* learnt_clauses;
        } fun;
    } representation;
    
    char type; // 0 indicates cegar round, 1 indicates case split
    // type listed last, as this reduces memory footprint of this struct by 7 bytes.
};

struct Casesplits {
    QCNF* qcnf;
    Skolem* skolem;
    Options* options;
    
    // dlvl0 interface
    int_vector* interface_vars;
    float_vector* interface_activities; // contains the frequencies of the interface variabes as floats
    map* original_satlits;
    
    vector* solved_cases; // over struct Case*
    
    // CEGAR
    SATSolver* exists_solver; // using original names, no redirect as in the skolem solver
    int_vector* is_used_in_lemma;
    int_vector* additional_assignment;
    struct Cegar_Statistics cegar_stats;
    struct Cegar_Magic_Values cegar_magic;
};

/* Initializes a cegar object, including the SAT solver using
 * the current determinicity information in c2->skolem.
 */
Casesplits* casesplits_init(QCNF*, Options*);
bool casesplits_is_initialized(Casesplits*);
void casesplits_free(Casesplits*);

void casesplits_record_case(Casesplits*, int_vector* decsisions);
void casesplits_completed_case_split(Casesplits*, int_vector* decisions, set* learnt_clauses);
void casesplits_completed_cegar_cube(Casesplits*, int_vector* cube, int_vector* partial_assignment);
void casesplits_encode_case_into_satsolver(Skolem*, Case* c, SATSolver* sat);
void casesplits_print_statistics(Casesplits*);

// Interface
void casesplits_update_interface(Casesplits*,Skolem*);
float casesplits_get_interface_activity(Casesplits*, unsigned var_id);
void casesplits_add_interface_activity(Casesplits*, unsigned var_id, float value);
void casesplits_decay_interface_activity(Casesplits*, unsigned var_id);

#endif /* c2_casesplits_h */
