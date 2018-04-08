//
//  c2_validate.h
//  cadet
//
//  Created by Markus Rabe on 25/12/2016.
//  Copyright © 2016 UC Berkeley. All rights reserved.
//

#ifndef c2_validate_h
#define c2_validate_h

#include "cadet_internal.h"

#include <stdio.h>

void c2_validate_var(Skolem*, unsigned var_id);
void c2_validate_unique_consequences(C2*);

#endif /* c2_validate_h */
