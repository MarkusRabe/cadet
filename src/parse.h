#ifndef __parse__
#define __parse__

#include "qcnf.h"
#include "options.h"

QCNF* create_qcnf_from_file(FILE*, Options*);
QCNF* create_qcnf_from_aiger(aiger*, Options*);

#endif /* defined(__parse__) */
