//
//  statistics.h
//  caqe
//
//  Created by Markus Rabe on 22/12/14.
//  Copyright (c) 2014 Saarland University. All rights reserved.
//

#ifndef __caqe__statistics__
#define __caqe__statistics__

#include "vector.h"
#include "int_vector.h"

typedef struct {
    size_t calls_num;
    double accumulated_value;
    double max;
    double min;
    int_vector* exponential_histogram; // stores the histogram of the logarithm of the microseconds.
    double factor; // factor applied to value before adding it to histogram
    double time_stamp;
    bool clock_is_running;
} Stats;

// Factor indicates the inverse resolution: 1000 corresponds to 1ms, 1 to 1s.
Stats* statistics_init(double factor);
void statistic_add_value(Stats* s, double v);
void statistics_print(Stats* s);
// For using it as a timer:
void statistics_start_timer(Stats* s);
double statistics_stop_and_record_timer(Stats* s);
bool statistics_timer_is_running(Stats* s);
void statistics_free(Stats*);

#endif /* defined(__caqe__statistics__) */
