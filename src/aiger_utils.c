//
//  aiger_utils.c
//  cadet
//
//  Created by Markus Rabe on 10/11/2016.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "aiger_utils.h"
#include "aiger.h"

int aiger_lit2lit(unsigned aigerlit) {
    int var = aiger_lit2var(aigerlit);
    return aigerlit % 2 ? - var : var;
}

unsigned inc(unsigned* sym) {
    *sym += 2;
    return *sym;
}

bool is_negated(unsigned signal) {
    return signal % 2; // negation is encoded in the last bit
}

unsigned negate(unsigned signal) {
    return signal ^ 1; // flipping the last bit with xor
}

unsigned var2aigerlit(unsigned var_id) {
    return 2 * var_id;
}
