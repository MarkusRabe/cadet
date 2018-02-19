//
//  statistics.c
//  caqe
//
//  Created by Markus Rabe on 22/12/14.
//  Copyright (c) 2014 Saarland University. All rights reserved.
//

#include "statistics.h"
#include "math.h"
#include "util.h"
#include "log.h"

#include <sys/time.h>
#include <assert.h>
#include <stdlib.h>

Stats* statistics_init(double factor) {
    Stats* s = malloc(sizeof(Stats));
    s->calls_num = 0;
    s->accumulated_value = 0.0;
    s->max = 0.0;
    s->min = 0.0;
    s->exponential_histogram = int_vector_init();
    s->factor = factor;
    s->time_stamp = 0.0;
    s->clock_is_running = false;
    return s;
}

void statistics_start_timer(Stats* s) {
    assert(! s->clock_is_running);
    s->time_stamp = get_seconds();
    s->clock_is_running = true;
}

double statistics_stop_and_record_timer(Stats* s) {
    if (! s->clock_is_running) {
        return 0.0;
    }
    double diff = get_seconds() - s->time_stamp;
    assert(diff >= 0.0); // time passed must be positive
    statistic_add_value(s, diff);
    s->clock_is_running = false;
    return diff;
}

bool statistics_timer_is_running(Stats* s) {
    return s->clock_is_running;
}

void statistic_add_value(Stats* s, double v) {
    assert(v>=0.0 && v < 9007199254740992.0); // maximally presented precise double ... not actually required, I guess
    // init
    if (s->calls_num == 0) {
        s->max = v;
        s->min = v;
    }
    // normal case:
    s->calls_num += 1;
    s->accumulated_value += v;
    if (v > s->max) {
        s->max = v;
    }
    if (v < s->min) {
        s->min = v;
    }
    long hist_value = lround(ceil(log2(s->factor * v))); // resolution is 0.1ms
    if (hist_value < 0) {
        hist_value = 0;
    }
    assert(hist_value < 100);
    while (((size_t) hist_value) >= int_vector_count(s->exponential_histogram)) {
        int_vector_add(s->exponential_histogram, 0);
    }
    int cur_value = int_vector_get(s->exponential_histogram, (unsigned) hist_value);
    int_vector_set(s->exponential_histogram, (unsigned) hist_value, cur_value + 1);
}

void statistics_print(Stats* s) {
    V0("    Average: %f\n", s->accumulated_value/s->calls_num);
    V0("    Total: %f\n", s->accumulated_value);
    V0("    Min/Max: %f/%f\n", s->min, s->max);
    V0("    Count: %zu\n", s->calls_num);
    V0("    Histogram:");

    for (unsigned i = 0; i < int_vector_count(s->exponential_histogram); i += 1) {
        if (s->factor != 10000) {
            printf("  <%f:", (exp2(i) / s->factor));
        }
        if ( s->factor == 10000 && i==0) {printf(" 0.1ms:");}
        if ( s->factor == 10000 && i==3) {printf("; 0.8ms:");}
        if ( s->factor == 10000 && i==6) {printf("; 6.4ms:");}
        if ( s->factor == 10000 && i==9) {printf("; 51.2ms:");}
        if ( s->factor == 10000 && i==12) {printf("; 409ms:");}
        if ( s->factor == 10000 && i==15) {printf("; 3.27s:");}
        printf(" %d",int_vector_get(s->exponential_histogram, i));
    }
    printf("\n");
}

void statistics_free(Stats* s) {
    int_vector_free(s->exponential_histogram);
    free(s);
}
