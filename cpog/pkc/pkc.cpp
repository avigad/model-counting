#include <cstdio>
#include <cstdlib>
#include <unistd.h>


#include "report.h"
#include "counters.h"
#include "project.hh"


void usage(const char *name) {
    lprintf("Usage: %s [-h] [-v VLEVEL] FORMULA.cnf FORMULA.pog\n", name);
    lprintf("  -h          Print this information\n");
    lprintf("  -v VERB     Set verbosity level\n");
}

static int run(const char *cnf_name) {
    Project proj(cnf_name);
    return 0;
}

int main(int argc, char *const argv[]) {
    FILE *cnf_file = NULL;
    verblevel = 1;
    int c;
    while ((c = getopt(argc, argv, "hv:")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	    return 0;
	case 'v':
	    verblevel = atoi(optarg);
	    break;
	default:
	    lprintf("Unknown comandline option '%c'\n", c);
	    usage(argv[0]);
	    break;
	}

    }
    int argi = optind;
    if (argi >= argc) {
	lprintf("Name of input CNF file required\n");
	usage(argv[0]);
	return 1;
    }
    int result = run(argv[argi]);
    return result;
}
