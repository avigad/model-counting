#include <cstdio>
#include <cstdlib>
#include <unistd.h>


#include "report.h"
#include "counters.h"
#include "clause.hh"
#include "pog.hh"

void usage(const char *name) {
    lprintf("Usage: %s [-h] [-v VLEVEL] FORMULA.cnf FORMULA.pog\n", name);
    lprintf("  -h          Print this information\n");
    lprintf("  -v VERB     Set verbosity level\n");
}

static int run(FILE *cnf_file) {
    Cnf cnf;
    cnf.import_file(cnf_file);
    fprintf(stdout, "Initial file:\n");
    if (cnf.is_loaded()) {
	cnf.write(stdout);
    } else {
	err(false, "Failed to load CNF file\n");
	return 1;
    }
    Clausal_reasoner cr(&cnf);
    bool conflict = cr.bcp(100);
    bool sat = cr.is_satisfiable();
    fprintf(stdout, "Running SAT solver gives result '%s' [time = %.3f secs)\n", sat ? "Satisifiable" : "Not satisfiable", get_timer(TIME_SAT));
    cnf_archive_t arx = cr.extract();
    cnf.deallocate();
    Cnf ncnf;
    ncnf.import_archive(arx);
    fprintf(stdout, "After BCP (conflict = %s):\n", conflict ? "true" : "false");    
    ncnf.write(stdout);
    ncnf.deallocate();
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
    cnf_file = fopen(argv[argi], "r");
    if (cnf_file == NULL) {
	lprintf("Can't open '%s'\n", argv[argi]);
	return 1;
    }
    int result = run(cnf_file);
    fclose(cnf_file);
    return result;
}
