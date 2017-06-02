//
//  function_encoding.h
//  cadet
//
//  Created by Markus Rabe on 01.06.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//
//  Provides higher-level features of the "function" representation that require access to Skolem itself.
//
//

#ifndef function_encoding_h
#define function_encoding_h

#include "skolem.h"

void f_add_clauses(Skolem*, unsigned var_id, vector* occs);

//void f_propagate_partial_over_clause_for_lit(Skolem*, Clause*, Lit, bool define_both_sides);
bool f_encode_unique_antecedents_for_lits(Skolem*, Lit, bool define_both_sides);

#endif /* function_encoding_h */
