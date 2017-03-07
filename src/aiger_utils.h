//
//  aiger_utils.h
//  cadet
//
//  Created by Markus Rabe on 10/11/2016.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef aiger_utils_h
#define aiger_utils_h

#include <stdio.h>

int aiger_lit2lit(unsigned aigerlit);
unsigned inc(unsigned* sym);
unsigned negate(unsigned signal);
unsigned var2aigerlit(unsigned var_id);

#endif /* aiger_utils_h */
