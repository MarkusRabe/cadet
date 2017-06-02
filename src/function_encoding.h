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

void f_add_clauses(Skolem* s, unsigned var_id, vector* occs);


typedef enum FIX_UNIQUE_ANTECEDENTS_MODE {
    FUAM_ONLY_LEGALS = 2,
    //    FUAM_IGNORE_ILLEGAL_DEP_LITERALS = 4,
} FIX_UNIQUE_ANTECEDENTS_MODE;
bool f_encode_unique_antecedents_for_lits(Skolem* s, Lit lit, bool define_both_sides, FIX_UNIQUE_ANTECEDENTS_MODE fuam);

#endif /* function_encoding_h */
