//
//  c2_cert.h
//  cadet
//
//  Created by Markus Rabe on 21/09/16.
//  Copyright © 2016 Saarland University. All rights reserved.
//

#ifndef c2_cert_h
#define c2_cert_h

#include "qcnf.h"
#include "options.h"
#include "aiger.h"
#include "cadet2.h"

#include <stdio.h>

void c2_cert_AIG_certificate(C2* c2);
void c2_print_qdimacs_certificate(C2* c2, void* domain, int (*get_value)(void* domain, Lit lit, bool second_copy));
bool c2_cert_check_UNSAT(QCNF* qcnf, void* domain, int (*get_value)(void* domain, Lit lit, bool second_copy));

//int aiger_lit2lit(unsigned aigerlit);

#endif /* certificates_h */
