#include <cstdio>
#include <cstdlib>
#include <unistd.h>


#include "report.h"
#include "counters.h"
#include "project.hh"


void usage(const char *name) {
    lprintf("Usage: %s [-h] [-k] [-v VLEVEL] FORMULA.cnf FORMULA.pog\n", name);
    lprintf("  -h          Print this information\n");
    lprintf("  -k          Keep intermdiate files\n");
    lprintf("  -v VERB     Set verbosity level\n");
}

static int run(const char *cnf_name, const char *pog_name) {
    Project proj(cnf_name);
    if (verblevel >= 5) {
	printf("Initial POG:\n");
	proj.show(stdout);
    }
    proj.projecting_compile();
    if (verblevel >= 5) {
	printf("Projected POG:\n");
	proj.show(stdout);
    }
    proj.write(pog_name);
    return 0;
}

int main(int argc, char *const argv[]) {
    FILE *cnf_file = NULL;
    verblevel = 1;
    bool keep = false;
    int c;
    double start = tod();
    while ((c = getopt(argc, argv, "hkv:")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	    return 0;
	case 'v':
	    verblevel = atoi(optarg);
	    break;
	case 'k':
	    keep = true;
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
    const char *cnf_name = argv[argi++];
    if (argi >= argc) {
	lprintf("Name of output POG file required\n");
	usage(argv[0]);
	return 1;
    }
    const char *pog_name = argv[argi++];
    if (argi < argc) {
	lprintf("Unknown argument '%s'", argv[argi]);
	usage(argv[0]);
	return 1;
    }
    int result = run(cnf_name, pog_name);
    double elapsed = tod() - start;
    
    lprintf("Total execution %.2f seconds\n", elapsed);
    if (!keep)
	fmgr.flush();
    return result;
}
