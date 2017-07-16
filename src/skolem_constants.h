//
//  skolem_constants.h
//  cadet
//
//  Created by Markus Rabe on 12.07.17.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef skolem_constants_h
#define skolem_constants_h

#include "skolem.h"

bool skolem_lit_satisfied(Skolem* s, Lit lit);
bool skolem_clause_satisfied(Skolem* s, Clause* c);

int skolem_get_constant_value(Skolem* s, Lit lit); // get the value of the variable, if it is a constant

#endif /* skolem_constants_h */
