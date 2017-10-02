//
//  qcnf.h
//  cadet
//
//  Created by Markus Rabe on 14/06/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef qcnf_h
#define qcnf_h

#include "vector.h"
#include "var_vector.h"
#include "map.h"
#include "undo_stack.h"

#include <stdbool.h>
#include <limits.h>

struct Clause;
typedef struct Clause Clause;
struct Var;
typedef struct Var Var;
typedef int Lit;
struct QCNF;
typedef struct QCNF QCNF;
struct Scope;
typedef struct Scope Scope;

struct C2_VAR_DATA {
//    unsigned phase : 1;
    float activity;
};
typedef struct C2_VAR_DATA C2_VAR_DATA;
C2_VAR_DATA c2_initial_var_data();

typedef enum {
    QCNF_PROPOSITIONAL,
    QCNF_2QBF,
    QCNF_QBF,
    QCNF_DQBF
} PROBLEM_TYPE;

struct Clause {
    unsigned clause_id; // is not needed, but convenient. Is not reconstructible like the var_ids

    unsigned int original                  : 1;
    unsigned int consistent_with_originals : 1;   // learnt clauses
    unsigned int PG                        : 1;   // Introduced throug Plaisted-Greenbaum completion
    unsigned int size                      : 29;
    
    // skolem_clause_info ... // contains unique_consequence
    
    Lit occs[1]; // to avoid flexible array member and make code compatible with newer C standards
};

struct Var {
    unsigned var_id; // not really needed; is "(v - qcnf->vars->data) >> log(size_of void*)"
    
    unsigned short scope_id;
    char is_universal; // just a boolean value
    char original; // just a boolean value
    
    // CADET2 data
    struct C2_VAR_DATA c2_vd;
    
    vector pos_occs; // vector of Clause*
    vector neg_occs;
    
    // Domains
    // PA_INFO pa_var  // contains just the cause of bcp; can we avoid that and encode it in the unique_consequences of clauses?
    // SKOLEM_VAR skolem_var
}; // should have length of 48 byte because of 64 bit alignment


// Set of universals.
// Assume: dozens to thousands of basic elements, but relatively few sets.
// Emptiness? creating a new set as the intersection of two others, efficient inclusion check.
struct Scope {
    int_vector* vars; // var_ids of its universals
};

struct QCNF {
    var_vector* vars; // indexed by var_id
    vector* clauses; // indexed by clause_id --- but it is deprecated to rely on this indexing
    vector* cubes; // cubes represented as clauses -- not indexed by anything. Only used for conversion from 3QBF 
    unsigned next_free_clause_id;
    
    vector* scopes; // vector of scope, indexed by scope_id.
    
    PROBLEM_TYPE problem_type;
    
    int_vector* new_clause;
    Clause* empty_clause; // is NULL if no empty clause exists
    
    int_vector* universals_constraints;
    
    Stack* stack;
    
    // Stats
    unsigned universal_reductions;
};

// Constructor and Destructor
QCNF* qcnf_init();
void qcnf_free();

//bool qcnf_is_2QBF(QCNF*);

void qcnf_push(QCNF*);
void qcnf_pop(QCNF*);

bool qcnf_contains_empty_clause(QCNF*);
bool qcnf_is_trivially_true(QCNF*);
bool qcnf_is_propositional(QCNF*);
bool qcnf_is_2QBF(QCNF*);
bool qcnf_is_DQBF(QCNF*);
bool qcnf_var_has_unique_maximal_dependency(QCNF*, unsigned var_id);

// Clauses
//bool contains_literal(Clause* clause, Lit lit);
bool qcnf_contains_literal(Clause*,Lit); // 0 if not contained, return lit if it occurs, and return -lit if the opposite lit occurs.
int qcnf_contains_variable(Clause*,Var*); // 0 if not contained, otherwise return lit.
//int qcnf_maximal_qlvl(QCNF*,Clause*);
//int qcnf_minimal_qlvl(QCNF*,Clause*);
bool qcnf_is_duplicate(QCNF*,Clause*);
bool qcnf_is_resolvent_tautological(Clause*, Clause*, unsigned var_id);
bool qcnf_antecedent_subsubsumed(QCNF*, Clause* c1, Clause* c2, unsigned var_id); // does c1 subsume c2 excluding occurrences of var_id?


// Variables
Var* qcnf_new_var(QCNF*, bool is_universal, unsigned scope_id, unsigned var_id);
bool qcnf_var_exists(QCNF*, unsigned var_id);
Var* qcnf_fresh_var(QCNF*, unsigned scope_id);
bool qcnf_is_existential(QCNF* qcnf, unsigned var_id);
bool qcnf_is_universal(QCNF* qcnf, unsigned var_id);
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
    QCNF_OP_NEW_VAR,
    QCNF_UPDATE_EMPTY_CLAUSE
} qcnf_op;

void qcnf_undo_op(void* qcnf,char,void*);



void qcnf_register_clause(QCNF*, Clause*);
void qcnf_unregister_clause(QCNF*, Clause*);
bool qcnf_remove_literal(QCNF*, Clause*, Lit);

void qcnf_plaisted_greenbaum_completion(QCNF* qcnf);

#endif /* qcnf_h */
