/*========================================================================
  Copyright (c) 2023 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of
  charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the
  Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom
  the Software is furnished to do so, subject to the following
  conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
========================================================================*/


#pragma once

#include "ilist.h"

// Count all the interesting stuff

typedef enum { 
    COUNT_INPUT_VAR, COUNT_INPUT_CLAUSE, COUNT_DATA_VAR,
    COUNT_POG_INITIAL_PRODUCT, COUNT_POG_INITIAL_SUM, COUNT_POG_INITIAL_EDGES,
    COUNT_POG_FINAL_PRODUCT, COUNT_POG_FINAL_SUM, COUNT_POG_FINAL_EDGES,
    COUNT_POG_PRODUCT, COUNT_POG_SUM, COUNT_POG_EDGES,
    COUNT_VISIT_PRODUCT, COUNT_VISIT_DATA_SUM, COUNT_VISIT_MUTEX_SUM, COUNT_VISIT_EXCLUDING_SUM,
    COUNT_SAT_CALL, COUNT_KC_CALL,
    COUNT_NUM
} counter_t;

typedef enum { TIME_SAT, TIME_KC, TIME_INITIAL_KC, TIME_NUM } timer_t;

typedef enum { HISTO_SAT_CLAUSES, HISTO_KC_CLAUSES, HISTO_POG_NODES, HISTO_NUM } histogram_t;

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

#ifdef CPLUSPLUS
extern "C" {
#endif

void incr_count(counter_t counter);
void incr_count_by(counter_t counter, int val);
int get_count(counter_t counter);

void incr_timer(timer_t timer, double secs);
double get_timer(timer_t timer);

void incr_histo(histogram_t h, int datum);
ilist get_histo(histogram_t h);

#ifdef CPLUSPLUS
}
#endif


/* EOF */
    
