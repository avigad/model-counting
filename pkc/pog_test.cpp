#include <cstdio>
#include <cstdlib>
#include <unistd.h>


#include "report.h"
#include "counters.h"
#include "pog.hh"

void usage(const char *name) {
    lprintf("Usage: %s [-h] [-n NVAR] [-v VLEVEL] ROOT1 ROOT2  ...\n", name);
    lprintf("  -h          Print this information\n");
    lprintf("  -v VERB     Set verbosity level\n");
    lprintf("  -n NVAR     Set number of input variables\n");
}

Pog *pog;

static int run(char *root_name) {
    char buf[1000];
    snprintf(buf, 1000, "%s.nnf", root_name);
    FILE *infile = fopen(buf, "r");
    if (!infile) {
	printf("Couldn't open file '%s'\n", buf);
	return 1;
    }
    int root = pog->load_nnf(infile);
    fclose(infile);
    printf("Got root %d\n", root);
    if (verblevel >= 2)
	pog->show(stdout);
    snprintf(buf, 1000, "%s.pog", root_name);
    FILE *outfile = fopen(buf, "w");
    if (!outfile) {
	printf("Couldn't open file '%s'\n", buf);
	return 1;
    }
    pog->write(root, outfile);
    fclose(outfile);
    printf("File %s written\n", buf);
    return 0;
}

int main(int argc, char *const argv[]) {
    FILE *nnf_file = NULL;
    verblevel = 1;
    int nvar = 100;
    int c;
    while ((c = getopt(argc, argv, "hn:v:")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	    return 0;
	case 'v':
	    verblevel = atoi(optarg);
	    break;
	case 'n':
	    nvar = atoi(optarg);
	    break;
	default:
	    lprintf("Unknown comandline option '%c'\n", c);
	    usage(argv[0]);
	    break;
	}

    }
    pog = new Pog(nvar);
    int argi = optind;
    if (argi >= argc) {
	lprintf("Name of input NNF file required\n");
	usage(argv[0]);
	return 1;
    }
    int result = 0;
    while (result == 0 && argi < argc) {
	result = run(argv[argi]);
	argi++;
    }
    return result;
}
