//
//  main.c
//  tests
//
//  Created by Markus Rabe on 28.03.18.
//  Copyright © 2018 UC Berkeley. All rights reserved.
//

#include "log.h"
#include "util.h"
#include "cadet2.h"

#include <stdbool.h>
#include <stdio.h>
#include <errno.h>
#include <time.h>


void test_read_and_solve(char* file_name) {
    V0("Processing file \"%s\".\n", file_name);
    FILE* file = open_possibly_zipped_file(file_name);
    Options* o = default_options();
    o->random_decisions = true;
    C2* c2 = c2_from_file(file, o);
    c2_sat(c2);
    close_possibly_zipped_file(file_name, file);
    c2_free(c2);
}


void test_repeated_solving() {
    for (unsigned i = 0; i < 100; i++) {
        test_read_and_solve("/Users/markus/work/cadet/dev/integration-tests/888_SAT.qdimacs");
        test_read_and_solve("/Users/markus/work/cadet/dev/integration-tests/1_SAT.dimacs.gz");
        test_read_and_solve("/Users/markus/work/cadet/dev/integration-tests/2_UNSAT.dimacs.gz");
    }
}

void test_all() {
    test_repeated_solving();
}
