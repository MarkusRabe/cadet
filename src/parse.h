#ifndef __caqe__parse__
#define __caqe__parse__

#include "matrix.h"
#include "qcnf.h"
#include "options.h"

Matrix* create_matrix_from_qdimacs(FILE*);
QCNF* create_qcnf_from_file(FILE*, Options*);
QCNF* create_qcnf_from_aiger(aiger*, Options*);
#endif /* defined(__caqe__parse__) */
