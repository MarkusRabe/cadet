//
//  qipasir_parser.h
//
//  A parser for QDIMACS files based on the qipasir API.
//

#ifndef qipasir_parser_h
#define qipasir_parser_h

#include <stdio.h>

/**
 * Parses the file file_name. If file_name ends on .gz the file is unzipped using gunzip.
 */
void* qipasir_parser_open_and_read_file(const char* file_name);
void* create_solver_from_qdimacs(FILE* file);

#endif /* qipasir_parser_h */
