//
//  qbf2aiger.h
//  cadet
//
//  Created by Markus Rabe on 06/01/2017.
//  Copyright © 2017 UC Berkeley. All rights reserved.
//

#ifndef qbf2aiger_h
#define qbf2aiger_h

#include "cadet2.h"
#include "aiger.h"

#include <stdio.h>

void reencode_existentials(QCNF* qcnf, Options* o);
aiger* qbf2aiger(QCNF*,Options*);

#endif /* qbf2aiger_h */
