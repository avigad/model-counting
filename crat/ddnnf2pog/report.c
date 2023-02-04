#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include "report.h"

int verblevel = 1;

FILE *errfile = NULL;
FILE *verbfile = NULL;

void set_verblevel(int level) {
    verblevel = level;
}

void err(bool fatal, const char *fmt, ...) {
    if (!errfile)
	errfile = stdout;
    va_list ap;
    va_start(ap, fmt);
    if (fatal)
	fprintf(errfile, "ERROR: ");
    else
	fprintf(errfile, "WARNING: ");
    vfprintf(errfile, fmt, ap);
    fflush(errfile);
    va_end(ap);
    if (fatal)
	exit(1);
}

void report(int level, const char *fmt, ...) {
    if (!verbfile)
	verbfile = stdout;
    va_list ap;
    if (level <= verblevel) {
	va_start(ap, fmt);
	vfprintf(verbfile, fmt, ap);
	fflush(verbfile);
	va_end(ap);
    }
}

double tod() {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) == 0)
	return (double) tv.tv_sec + 1e-6 * tv.tv_usec;
    else
	return 0.0;
}
