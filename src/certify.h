//
//  certify.h
//  cadet
//
//  Created by Markus Rabe on 21/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef certify_h
#define certify_h

#include "qcnf.h"
#include "options.h"
#include "aiger.h"
#include "cadet2.h"

#include <stdio.h>

void cert_AIG_certificate(C2* c2);
void c2_print_qdimacs_output(int_vector* refuting_assignment);
bool cert_check_UNSAT(C2*);
void cert_propositional_AIG_certificate_SAT(QCNF* qcnf, Options* o, void* domain, int (*get_value)(void* domain, Lit lit));

bool cert_check_SAT(C2* c2);

#endif /* certificates_h */
