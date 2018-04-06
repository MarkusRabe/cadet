//
//  aiger_utils.h
//  cadet
//
//  Created by Markus Rabe on 10/11/2016.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef aiger_utils_h
#define aiger_utils_h

#include "aiger.h"
#include "int_vector.h"

#include <stdbool.h>

int aiger_lit2lit(unsigned aigerlit, int truelit); // truelit indicates a literal that represents true
unsigned inc(unsigned* sym);
bool is_negated(unsigned signal);
unsigned negate(unsigned signal);
unsigned var2aigerlit(unsigned var_id);


void aigeru_add_multiAND(aiger* a, unsigned* max_sym, unsigned output_aigerlit, int_vector* input_aigerlits);
void aigeru_add_OR(aiger* a, unsigned* max_sym, unsigned output_aigerlit, unsigned i1, unsigned i2);
void aigeru_add_multiOR(aiger* a, unsigned* max_sym, unsigned output_aigerlit, int_vector* input_aigerlits);
void aigeru_add_multiplexer(aiger* a, unsigned* max_sym,
                            unsigned output, unsigned selector, unsigned if_signal, unsigned else_signal);
unsigned aigeru_MUX(aiger* a, unsigned* max_sym, unsigned selector, unsigned i1, unsigned i2);
unsigned aigeru_multiMUX(aiger* a, unsigned* max_sym, int_vector* selectors, int_vector* inputs);

unsigned aigeru_OR(aiger* a, unsigned* max_sym, unsigned i1, unsigned i2);
unsigned aigeru_AND(aiger* a, unsigned* max_sym, unsigned i1, unsigned i2);
unsigned aigeru_multiOR(aiger* a, unsigned* max_sym, int_vector* input_aigerlits);
unsigned aigeru_multiAND(aiger* a, unsigned* max_sym, int_vector* input_aigerlits);


#endif /* aiger_utils_h */
