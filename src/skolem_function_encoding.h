//
//  skolem_function_encoding.h
//  cadet
//
//  Created by Markus Rabe on 01.06.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//
//  Provides higher-level features of the "function" representation that require access to Skolem itself.
//
//

#ifndef skolem_function_encoding_h
#define skolem_function_encoding_h

#include "skolem.h"

struct Function_encoding;

void f_add_clauses(Skolem*, unsigned var_id, vector* occs);

//void f_propagate_partial_over_clause_for_lit(Skolem*, Clause*, Lit, bool define_both_sides);
bool f_encode_unique_antecedents_for_lits(Skolem*, Lit, bool define_both_sides);

void f_encode_give_fresh_satlit(Skolem* s, unsigned var_id);

void f_add_satlit_clause(Function*, const vector*); // vector of satlits
void f_add_lit_clause_for_context(Skolem* s, const int_vector* clause, unsigned context);

satlit f_add_AND(Function*, satlit input1, satlit input2);
satlit f_add_OR(Function*, satlit input1, satlit input2);

void f_encode_conflictedness(Skolem*, unsigned var_id); // Add two clauses saying that the variable is true and false at the same time. Needed for global conflictedness check.

#endif /* skolem_function_encoding_h */
