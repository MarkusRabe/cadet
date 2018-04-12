//
//  qcnf.h
//  cadet
//
//  Created by Markus Rabe on 14/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef qcnf_h
#define qcnf_h

#include "int_vector.h"
#include "vector.h"
#include "var_vector.h"
#include "map.h"
#include "undo_stack.h"

#include <stdbool.h>
#include <limits.h>

struct Clause;
typedef struct Clause Clause;
struct Clause_Iterator;
typedef struct Clause_Iterator Clause_Iterator;
struct Var;
typedef struct Var Var;
typedef int Lit;
struct QCNF;
typedef struct QCNF QCNF;
struct Scope;
typedef struct Scope Scope;

typedef enum {
    QCNF_PROPOSITIONAL,
    QCNF_2QBF,
    QCNF_QBF,
    QCNF_DQBF
} PROBLEM_TYPE;

struct Clause {
    unsigned int clause_idx; // its position in the clause vector; can change, unlike var_ids

    unsigned int original                  : 1;
    unsigned int consistent_with_originals : 1;   // learnt clauses
    unsigned int blocked                   : 1;   // for blocked clause elimination
    unsigned int universal_clause          : 1;   // contains only universals
    unsigned int is_cube                   : 1;   // A clause that intentionally excludes universal assignments
    unsigned int minimized                 : 1;   // Indicates the clause has been simplified
    unsigned int active                    : 1;   // inactive clauses are not needed anymore, but are still in all_clauses
    unsigned int in_active_clause_vector   : 1;   // inactive clauses are deleted lazily from the active clause vector; this bit indicates this list has not yet been thrown out
    unsigned int size                      : 24;
    
    Lit occs[1]; // to avoid flexible array member and make code compatible with newer C standards
};

struct Clause_Iterator {
    QCNF* qcnf;
    size_t clause_iterator_token;
    unsigned idx; // the NEXT position in the vector of active clauses
};

struct Var {
    unsigned var_id; // not really needed; is "(v - qcnf->vars->data) >> log(size_of void*)"
    
    unsigned short scope_id;
    char is_universal; // just a boolean value
    char original; // just a boolean value
    
    vector pos_occs; // vector of Clause*
    vector neg_occs;
}; // should have length of 48 byte because of 64 bit alignment


// Set of universals.
// Assume: dozens to thousands of basic elements, but relatively few sets.
// Emptiness? creating a new set as the intersection of two others, efficient inclusion check.
struct Scope {
    int_vector* vars; // var_ids of its universals
};

struct QCNF {
    var_vector* vars; // indexed by var_id
    vector* all_clauses; // indexed by clause_idx
    vector* active_clauses; // indexed by clause_idx
    size_t clause_iterator_token; // makes sure that only one clause iterator is active at any point
    vector* scopes; // vector of scope, indexed by scope_id.
    PROBLEM_TYPE problem_type;
    
    int_vector* new_clause;
    int_vector* universal_clauses; // idxs of clauses containing only universals
    
    Stack* stack;
    
    vector* variable_names;
    
    // Stats
    unsigned universal_reductions;
    unsigned deleted_clauses;
    unsigned blocked_clauses;
};

// Constructor and Destructor
QCNF* qcnf_init();
void qcnf_free(QCNF*);
QCNF* qcnf_copy(QCNF*);
//bool qcnf_is_2QBF(QCNF*);

void qcnf_push(QCNF*);
void qcnf_pop(QCNF*);

bool qcnf_contains_clause_with_only_universals(QCNF*);
bool qcnf_is_trivially_true(QCNF*);
bool qcnf_is_propositional(QCNF*);
bool qcnf_is_2QBF(QCNF*);
bool qcnf_is_DQBF(QCNF*);
bool qcnf_var_has_unique_maximal_dependency(QCNF*, unsigned var_id);

// Clauses
//bool contains_literal(Clause* clause, Lit lit);
bool qcnf_contains_literal(Clause*,Lit); // 0 if not contained, return lit if it occurs, and return -lit if the opposite lit occurs.
int qcnf_contains_variable(Clause*,Var*); // 0 if not contained, otherwise return lit.
bool qcnf_check_if_clause_is_universal(QCNF*, Clause*);
bool qcnf_is_learnt_clause(Clause*);
bool qcnf_is_learnt_clause_idx(QCNF*, unsigned clause_idx);
bool qcnf_is_original_clause(QCNF*, unsigned clause_idx);
bool qcnf_is_active(QCNF*, unsigned clause_idx);
//int qcnf_maximal_qlvl(QCNF*,Clause*);
//int qcnf_minimal_qlvl(QCNF*,Clause*);
bool qcnf_is_duplicate(QCNF*,Clause*);
bool qcnf_is_resolvent_tautological(QCNF*, Clause*, Clause*, unsigned var_id);
bool qcnf_antecedent_subsubsumed(QCNF*, Clause* c1, Clause* c2, unsigned var_id); // does c1 subsume c2 excluding occurrences of var_id?


// Variables
Var* qcnf_new_var(QCNF*, bool is_universal, unsigned scope_id, unsigned var_id);
bool qcnf_var_exists(QCNF*, unsigned var_id);
unsigned qcnf_fresh_universal(QCNF*);
bool qcnf_is_existential(QCNF* qcnf, unsigned var_id);
bool qcnf_is_universal(QCNF* qcnf, unsigned var_id);
bool qcnf_is_original(QCNF* qcnf, unsigned var_id);
vector* qcnf_get_occs_of_lit(QCNF* qcnf, Lit lit);

void qcnf_add_lit(QCNF*, int lit);
Clause* qcnf_close_clause(QCNF*);
Clause* qcnf_new_clause(QCNF* qcnf, int_vector* literals);

// Scopes
unsigned qcnf_scope_init(QCNF*, int_vector* vars); // Attention: vars may be disallocated.
unsigned qcnf_scope_init_as_intersection(QCNF*, Scope*, Scope*);
//bool qcnf_scope_includes(Domain* d1, unsigned d2_id);
void qcnf_scope_free(Scope*);
//void qcnf_close_scopes_under_intersection(QCNF*);
unsigned qcnf_get_empty_scope(QCNF*);

// Comparators
int qcnf_compare_clauses_by_size (const void * a, const void * b);
int qcnf_compare_occurrence_by_qtype_then_scope_size_then_var_id(QCNF*, const void * a, const void * b);
int qcnf_compare_literal_pointers_by_var_id(const void * a, const void * b);
int qcnf_compare_literals_by_var_id(const void * a, const void * b);
int qcnf_compare_variables_by_occ_num(const void * a, const void * b);

void qcnf_convert_to_DQBF(QCNF* qcnf);


// Printing
void qcnf_print_clause(Clause*, FILE* f);
void qcnf_print_qdimacs(QCNF*);
void qcnf_print_qdimacs_quantifiers(QCNF* qcnf, FILE* f);
void qcnf_print_qdimacs_file(QCNF* m, FILE* f);
void qcnf_print_debug(QCNF*);

void qcnf_print_statistics(QCNF* qcnf);

// Invariants
void qcnf_check_invariants(QCNF* qcnf);

// PRIVATE FUNCTIONS

// Undo

typedef enum {
    QCNF_OP_NEW_CLAUSE,
    QCNF_OP_NEW_VAR
} qcnf_op;

void qcnf_undo_op(void* qcnf,char,void*);

bool qcnf_register_clause(QCNF*, Clause*);
void qcnf_unregister_clause(QCNF*, Clause*);
bool qcnf_remove_literal(QCNF*, Clause*, Lit);
void qcnf_delete_clause(QCNF*, Clause*);

void qcnf_plaisted_greenbaum_completion(QCNF* qcnf);
void qcnf_blocked_clause_detection(QCNF* qcnf);
bool qcnf_is_blocked_by_lit(QCNF* qcnf, Clause* c, Lit pivot);
bool qcnf_is_blocked(QCNF* qcnf, Clause* c);

Clause_Iterator qcnf_get_clause_iterator(QCNF*);
Clause* qcnf_next_clause(Clause_Iterator*);

char* qcnf_get_variable_name(QCNF*, unsigned var_id);
void qcnf_set_variable_name(QCNF*, unsigned var_id, const char* name);


#endif /* qcnf_h */
