//
//  reactive.h
//  caqe
//
//  Created by Markus Rabe on 16/03/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef reactive_h
#define reactive_h

#include "options.h"
#include <stdio.h>

int reactive(FILE*, Options*);

bool is_controllable(const char* str);

#endif /* reactive_h */
