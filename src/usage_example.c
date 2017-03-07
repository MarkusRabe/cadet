//
//  usage_example.c
//  caqe
//
//  Created by Markus Rabe on 08/03/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#include "cadet.h"
#include "assert.h"

void test_interface() {
    
    CADET* cadet = cadet_init();
    cadet_new_universal_quantifier(cadet);
    cadet_create_var(cadet, 1);
    cadet_create_var(cadet, 2);
    cadet_new_existential_quantifier(cadet);
    cadet_create_var(cadet, 3);
    
    // encode an AND gate
    cadet_add_lit(cadet, 1);
    cadet_add_lit(cadet, -3);
    cadet_add_lit(cadet, 0);
    
    cadet_add_lit(cadet, 2);
    cadet_add_lit(cadet, -3);
    cadet_add_lit(cadet, 0);
    
    cadet_add_lit(cadet, -1);
    cadet_add_lit(cadet, -2);
    cadet_add_lit(cadet, 3);
    cadet_add_lit(cadet, 0);
    
    cadet_res res = cadet_solve(cadet);
    
    assert(res == CADET_RESULT_SAT);    
}
