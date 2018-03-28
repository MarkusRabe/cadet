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


bool test_read_and_solve(char* file_name) {
    V0("Processing file \"%s\".\n", file_name);
    FILE* file = open_possibly_zipped_file(file_name);
    c2_solve_qdimacs(file, NULL);
    return true;
}


void test_repeated_solving() {
    for (unsigned i = 0; i < 100; i++) {
        test_read_and_solve("/Users/markus/work/cadet/dev/integration-tests/888_SAT.qdimacs");
    }
}

void test_all() {
    test_repeated_solving();
}
