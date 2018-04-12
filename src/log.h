#ifndef log_h
#define log_h

#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <assert.h>

#define SATSOLVER_TRACE

#define VERBOSITY_ALL    4
#define VERBOSITY_HIGH   3
#define VERBOSITY_MEDIUM 2
#define VERBOSITY_LOW    1
#define VERBOSITY_NONE   0

#define KNRM  "\x1B[0m"
#define KRED  "\x1B[31m"
#define KGRN  "\x1B[32m"
#define KYEL  "\x1B[33m"
#define KBLU  "\x1B[34m"
#define KMAG  "\x1B[35m"
#define KCYN  "\x1B[36m"
#define KWHT  "\x1B[37m"

// More advanced colors from post of PLASMAROB http://unix.stackexchange.com/questions/124407/what-color-codes-can-i-use-in-my-ps1-prompt
#define KNRM_BOLD  "\x1B[01;38;5;0m"
#define KRED_BOLD  "\x1B[01;38;5;09m"
#define KGRN_BOLD  "\x1B[01;38;5;10m"
#define KYEL_BOLD  "\x1B[01;38;5;11m"
#define KBLU_BOLD  "\x1B[01;38;5;12m"
#define KMAG_BOLD  "\x1B[01;38;5;13m"
#define KCYN_BOLD  "\x1B[01;38;5;14m"
#define KWHT_BOLD  "\x1B[01;38;5;15m"

#define KORANGE  "\x1B[38;5;202m"
#define KORANGE_BOLD  "\x1B[01;38;5;202m"

int debug_verbosity;
bool log_qdimacs_compliant;
bool log_colors;
bool log_silent;

#pragma clang diagnostic push
#pragma clang diagnostic ignored "-Wgnu-zero-variadic-macro-arguments"

#define LOG_PRINTF(message, ...) if(log_silent){}else{if(log_qdimacs_compliant){ fprintf(stdout, "c ");}fprintf(stdout, message, ## __VA_ARGS__);}

#define V0(message, ...) if(true){LOG_PRINTF(message, ## __VA_ARGS__);}
#define V1(message, ...) if(debug_verbosity >= VERBOSITY_LOW){ LOG_PRINTF(message, ## __VA_ARGS__); }
#define V2(message, ...) if(debug_verbosity >= VERBOSITY_MEDIUM){ LOG_PRINTF("  "message, ## __VA_ARGS__); }
#define V3(message, ...) if(debug_verbosity >= VERBOSITY_HIGH){ LOG_PRINTF("    "message, ## __VA_ARGS__); }
#define V4(message, ...) if(debug_verbosity >= VERBOSITY_ALL){ LOG_PRINTF("      "message, ## __VA_ARGS__); }

#define NOT_IMPLEMENTED() LOG_COLOR(KCYN, "Not yet implemented, abort\n"); abort();

#define LOG_COLOR(color, message, ...) if(log_colors){V0("%s", color);}V0(message, ## __VA_ARGS__);if(log_colors){V0(KNRM);}
#define LOG_ERROR(message, ...) LOG_COLOR(KRED, "Error: "); fprintf(stdout, message "\n", ## __VA_ARGS__);
#define LOG_WARNING(message, ...) LOG_COLOR(KYEL, "Warning: "); V0(message "\n", ## __VA_ARGS__);

#define abortif(cond,message, ...) \
do { \
if (!(cond)) break; \
LOG_ERROR(message, ## __VA_ARGS__) \
abort(); \
} while (0)

#pragma clang diagnostic pop

#endif /* defined(__caqe__config__) */
