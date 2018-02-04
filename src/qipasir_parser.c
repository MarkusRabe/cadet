//
//  qipasir_parser.c
//
//  Created by Markus Rabe and Leander Tentrup
//

#include "qipasir_parser.h"
#include "qipasir.h"

#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>

#define GUNZIP "gunzip -c %s 2>/dev/null"

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"
#define abortif(cond,message, ...) \
do { \
if (!(cond)) break; \
printf("Error: "); \
printf(message, ## __VA_ARGS__); \
abort(); \
} while (0)
#pragma clang diagnostic pop

void* create_solver_from_qdimacs(FILE* file) {
    assert(file != NULL);
    
    void* solver = qipasir_init();
    
    int c;
    int var = -1;
    bool neg = false;
    int qlvl = 0;
    bool line_defines_quantifier = false;
    bool seen_header = false;
    
    int line_num = 1;
    int pos = 0;
    
    while ((c = (char) getc(file)) != EOF) {
        switch (c) {
            case 'c':  // comment
                while (getc(file) != '\n');
                if (seen_header) {printf("Warning: Comments after header not allowed in the QDIMACS standard.\n");}
                line_num++;
                pos = 0;
                break;
                
            case 'p':  // header
                while (getc(file) != '\n');
                line_num++;
                pos = 0;
                abortif(seen_header, "Found second header (line %d, pos %d)", line_num, pos);
                seen_header = true;
                break;
                
            case 'e': // existential quantifier
                if (qlvl%2 == 1) {
                    qlvl++;
                } else if (qlvl != 0) {
                    printf("Warning: Consecutive quantifiers of the same type are not allowed in the QDIMACS standard (line %d, pos %d). Continuing as if this quantifier was merged with the previous quantifier.\n", line_num, pos);
                }
                assert(qlvl%2 == 0);
                line_defines_quantifier = true;
                pos++;
                abortif(!seen_header, "Header missing (line %d, pos %d)\n", line_num, pos);
                break;
                
            case 'a': // universal quantifier
                if (qlvl%2 == 0) {
                    qlvl++;
                } else {
                    printf("Warning: Consecutive quantifiers of the same type are not allowed in the QDIMACS standard (line %d, pos %d). Continuing as if this quantifier was merged with the previous quantifier.\n", line_num, pos);
                }
                line_defines_quantifier = true;
                pos++;
                abortif(!seen_header, "Header missing (line %d, pos %d)\n", line_num, pos);
                break;

            case '\n':
            case ' ':
                if (var == -1) {
                    break;
                }
                assert(var >= 0);
                if (line_defines_quantifier) {
                    if (var != 0) {
                        abortif(neg, "Negation is not allowed in the definition of quantifiers (line %d, pos %d).\n", line_num, pos);
                        qipasir_new_variable(solver, var, qlvl);
                    }
                } else {
                    qipasir_add(solver, neg? -var : var);
                }
                var = -1;
                neg = false;
                pos++;
                if (c =='\n') {line_defines_quantifier = false; line_num++; pos = 0;}
                break;
                
            case '-':
                abortif(neg, "Double negation '--' is not allowed (line %d, pos %d).\n", line_num, pos);
                neg = true;
                pos++;
                break;
                
            case '0':
            case '1':
            case '2':
            case '3':
            case '4':
            case '5':
            case '6':
            case '7':
            case '8':
            case '9':
                if (var == -1) {
                    var = 0;
                }
                var = (var * 10) + (c - '0');
                pos++;
                abortif(!seen_header, "Header missing (line %d, pos %d)\n", line_num, pos);
                break;
                
            default:
                abortif(true, "Unknown character \"%c\" (line %d, pos %d)\n", c, line_num, pos);
        }
    }
    
    if (var == 0) { // in case EOF came just after the 0
        printf("Warning: QDIMACS format requires clauses and quantifiers to end with EOL (line %d, pos %d).\n", line_num, pos);
        var = -1;
        if (line_defines_quantifier) {
            line_defines_quantifier = false;
        } else {
            qipasir_add(solver, 0);
        }
    }
    
    abortif(!seen_header, "Header missing (line %d, pos %d)\n", line_num, pos);
    abortif(var != -1, "Clause not closed with 0 (line %d, pos %d).\n", line_num, pos);
    abortif(line_defines_quantifier, "Quantifier definition not closed with 0 (line %d, pos %d).\n", line_num, pos);
    
    return solver;
}

static bool has_suffix(const char* string, const char* suffix) {
    if (strlen(suffix) > strlen(string)) {
        return false;
    }
    if (strncmp(string + (strlen(string) - strlen(suffix)), suffix, strlen(suffix)) == 0) {
        return true;
    }
    return false;
}

void* qipasir_parser_open_and_read_file(const char* file_name) {
    FILE* file;
    bool use_pclose;
    
    if (has_suffix(file_name, ".gz")) {
        use_pclose = true;
        
        char* cmd = malloc(strlen(file_name) + strlen(GUNZIP));
        sprintf(cmd, GUNZIP, file_name);
        file = popen(cmd, "r");
        free(cmd);
    } else {
        file = fopen(file_name, "r");
        use_pclose = false;
    }
    
    if (!file) {
        abortif(true,"File \"%s\" does not exist!\n", file_name);
    }
    
    void* solver = create_solver_from_qdimacs(file);
    
    if (use_pclose) {
        pclose(file);
    } else {
        fclose(file);
    }
    
    return solver;
}
