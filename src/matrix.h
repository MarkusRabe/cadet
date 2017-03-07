//
//  matrix.h
//  caqe
//
//  Created by Markus Rabe on 21/11/14.
//  Copyright (c) 2014 Saarland University. All rights reserved.
//

#ifndef __caqe__matrix__
#define __caqe__matrix__

#include "vector.h"
#include "map.h"
#include "heap.h"
#include "satsolver.h"

#include <stdio.h>
#include <stdbool.h>
#include <limits.h>


typedef enum {
    MATRIX_SATISFIABLE,
    MATRIX_UNSATISFIABLE,
    MATRIX_UNKNOWN
} matrix_res;

typedef enum {
    QUANTIFIER_EXISTENTIAL,
    QUANTIFIER_UNIVERSAL
} quant;

typedef enum {
    MATRIX_OP_ASSIGN_MATRIX_RESULT,
    MATRIX_OP_CLAUSE_SATISFIED,
    MATRIX_OP_ASSIGN_VAR,
    MATRIX_OP_QBCE_ELIMINATION,
    MATRIX_OP_MILESTONE,
    MATRIX_OP_ADD_CLAUSE,
    MATRIX_OP_NEW_MAX_VAR,
    MATRIX_OP_DETERMINISTIC_VAR,
    MATRIX_OP_DECISION
} matrix_op;

struct MClause;
typedef struct MClause MClause;
struct MVar;
typedef struct MVar MVar;
struct Occ;
typedef struct Occ Occ;
struct MScope;
typedef struct MScope MScope;
struct Matrix;
typedef struct Matrix Matrix;

struct Operation;
typedef struct Operation Operation;

struct Operation {
    matrix_op type;
    union {
        Occ* occ;
        MVar* var;
        MClause* clause;
        matrix_res previous_result;
    };
};


/**
 * An occurrence of a variable in a clause. We could also call them literals, but literals exist independent of clauses.
 */
//struct Occ {
//    unsigned int direction : 1;
//    unsigned int neg : 1;
//    unsigned int var_id : 30;
//    MClause* clause; // do we really really need this? SAT solver seem to be fine without. Use clauses instead of occs in occurrence lists.
//};

struct Occ { // TODO: replace Occs by positive/negative integers. Occurrence lists then should be lists of clauses. See also above.
    bool neg;
    MVar* var;
    MClause* clause;
};

struct MClause {
    int clause_id; // corresponds to T variable num; TODO: can we remove it?
    
    unsigned int needs_propagation_check : 1;
    unsigned int learnt                  : 1;
    unsigned int original                : 1;
    unsigned int blocked                 : 1;
    unsigned int unconflicting           : 1;
    unsigned int size                    : 27;
    
    MClause* next;
    MClause* prev;
    
    // TODO: replace the following pointer by a single bit per occurrence?
    Occ* unique_consequence_occ; // A partial function case. The direction of propagation in this clause is always fixed.
    
    Occ* occs; // TODO: Occ occs[];
};

struct MVar {
    
    int var_id;
    int value : 2; // -1, 0, 1
    
    unsigned int needs_qbce_check : 1;
    unsigned int needs_determinicity_check : 1;
    unsigned int is_decision_var : 1;
    unsigned int is_helper : 1;
    unsigned int has_only_blocked_clauses : 1;
# define NO_DECISION 0
    unsigned int decision_level : 25;
    
    float activity;
    
#define NO_DEPENDENCE_LVL INT_MAX
    size_t dependence_level; // indicates the maximal quantifier level this variable depends on. Is NO_DEPENDENCE_LVL, if no dependece is set yet. Must be smaller or equal than its own quantifier level. Can be an existential level, e.g. if assigned  by a unit clause.
    
    // vector* defining_clauses; // TODO: can be removed. Instead rely on the unique_consequence_occ of the clauses in the occurrence list.
    
    // vectors of occurrences
    vector* pos_occs; // TODO: make both vectors members of this struct. The vector objects themselves never change size.
    vector* neg_occs;
    
    MScope* scope; // could be replaced by scope id for saving memory
    
//    MClause* pointed_to_in_implication_graph; // clauses that implied this variable. each such clause induces a set of variable assignments that influenced this variable potentially in this direction. This vector may be empty in case the variable is not set or it was assigned due to pure literal detection.
};

struct MScope {
    size_t level;
    bool deactivated;
    quant qtype;
    vector* vars;
};

// This data structure fulfills several purposes:
// (1) Efficient manipulation operations
// (2) Minimization throug propagation, pure literal detection, and universal reduction
// (3) Maintain occurrence lists
struct Matrix {
    MClause* first_clause;
    size_t clause_num;
    int max_clause_id;
    
    map* var_lookup; // maps var_id to MVar*
    int max_var_id;
    
    // Scopes
    vector* scopes;
    
    // Working queues
    heap* clauses_to_check; // for propagation
    heap* variables_to_check; // used for pure literal detection, QBCE
    
    heap* variables_to_check_for_determinicity;
    
    // Statistics
    size_t assigned_variables;
    size_t satisfied_clauses;
    size_t qbce_eliminated_clauses;
    size_t qbce_eliminated_vars;
    size_t removed_occurrences_from_occurrence_list;
    
    // Operation queue and backtracking
    Operation* op_vector;
    size_t op_size;
    size_t op_count;
    int push_count; // number of milestones in the op_vector
    int decision_level;
    size_t minimal_dependence_lvl; // the quantifier level of current decisions. Must be an even number, as existential quantifiers have even numbers.
    
    int_vector* new_clause;
    
    // Conflict
    MClause* conflicted_clause;
    
    size_t iteration_number;
    
    matrix_res result; // MATRIX_UNSATISFIABLE, MATRIX_UNKNOWN, or MATRIX_SATISFIABLE
};

// Constructors
Matrix* matrix_init();

// MVariables
MVar* matrix_add_variable_to_last_scope(Matrix*, int var);
MVar* matrix_new_var(Matrix*, MScope*, int var);
MVar* matrix_get_var(Matrix*, int var);
MVar* matrix_inc_max_var(Matrix*);

MClause* matrix_add_lit(Matrix* m, int lit);
MClause* matrix_add_lit_undoable(Matrix* m, int lit);

size_t compute_dependence_lvl(Matrix* m, MVar* v);

// MScopes
MScope* matrix_new_scope(Matrix*, quant);
MScope* matrix_get_last_scope(Matrix*);
void matrix_free_scope(MScope*);

// MClauses
MClause* matrix_new_clause(Matrix*, int_vector* literals);
int matrix_get_lit(Occ*);

bool has_illegal_dependence(MClause*);

int compare_clauses_by_size (const void * a, const void * b);
int compare_occurrence_by_level_then_var_id(const void * a, const void * b);
int compare_variables_by_occ_num(const void * a, const void * b);

// Propagation
void matrix_propagate(Matrix*);
void matrix_propagate_var(Matrix*, MVar*, int value);

MClause* matrix_conflict_clause(Matrix*);

// Optimization
void matrix_simplify(Matrix*);
void matrix_qbce_vars(Matrix*);
//void matrix_get_seperation(Matrix*);
//void matrix_create_fake_seperation(Matrix*);

// Printing:
void matrix_print_clause(MClause*, FILE* f);
void matrix_print_clause_debug(MClause* c);
void matrix_print_qdimacs(Matrix*);
void matrix_print_qdimacs_file(Matrix* m, FILE* f);
void matrix_print_debug(Matrix*);

// Maintenance and memory managemet:
Matrix* matrix_cleanup(Matrix*);
void matrix_free(Matrix*);

// Matrix manipulation
//void matrix_assume(Matrix*, int);
void matrix_assume(Matrix*, int, MVar*); // assumes a literal in O(1); does not yet propagate (use matrix_propagate)
void matrix_push_milestone(Matrix*);  // O(1)
void matrix_pop_milestone(Matrix*); // O(size of original matrix)
void matrix_undo_operation(Matrix*, Operation*);
void matrix_decision_var(Matrix*, MVar*);
void matrix_deterministic_var(Matrix*, MVar*);
void matrix_clause_satisfied(Matrix*, Occ*);
void matrix_remove_clause(Matrix*, MClause*);
Occ* is_clause_satisfied(MClause*);

// Matrix validation
void matrix_validate(Matrix*);
#endif /* defined(__caqe__matrix__) */

