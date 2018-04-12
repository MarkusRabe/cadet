//
//  qcnf_variable_names.c
//  cadet
//
//  Created by Markus Rabe on 11.04.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "qcnf.h"

#include <string.h>
#include <assert.h>

char* qcnf_get_variable_name(QCNF* qcnf, unsigned var_id) {
    assert(var_id != 0);
    if (var_id < vector_count(qcnf->variable_names)) {
        return vector_get(qcnf->variable_names, var_id);
    } else {
        return NULL;
    }
}


void qcnf_set_variable_name(QCNF* qcnf, unsigned var_id, const char* name) {
    while (vector_count(qcnf->variable_names) <= var_id) {
        vector_add(qcnf->variable_names, NULL);
    }
    char* copy = NULL;
    if (name) {
        copy = malloc(sizeof(char) * ((size_t) strlen(name) + 1));
        strcpy(copy, name);
    }
    vector_set(qcnf->variable_names, var_id, copy);
}
