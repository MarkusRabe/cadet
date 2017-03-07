//
//  certification.h
//  caqe
//
//  File created by Markus Rabe on 17/02/2016.
//  Copyright (c) 2016. All rights reserved.
//

#ifndef __caqe__certification__
#define __caqe__certification__

#include "matrix.h"
#include "options.h"
#include "aiger.h"

#include <stdio.h>

aiger* qbf_Skolem_certificate(Matrix* m, Options* options);
aiger* synthesis_certificate(aiger* problem, Matrix* m, Options* options);
aiger* synthesis_implementation(aiger* problem, Matrix* m, Options* options);

#endif /* defined(__caqe__certification__) */
