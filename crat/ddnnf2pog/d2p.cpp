// Translate DNNF representation into POG

// Usage: d2p [VLEVEL] file.cnf file.d4nnf

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "report.h"
#include "clause.hh"
#include "pog.hh"

int main(int argc, const char *argv[]) {
    int cid = 0;
    FILE *cfile = NULL;
    FILE *nfile = NULL;
    verblevel = 1;
    if (argc <= 1 || strcmp(argv[1], "-h") == 0) {
	printf("Usage: %s [VLEVEL] CNF D4NNF\n", argv[0]);
	exit(0);
    }
    int argi = 1;
    if (isdigit(*argv[argi])) {
	verblevel = atoi(argv[argi]);
	argi++;
    }
    if (argi >= argc) {
	printf("Usage: %s [VLEVEL] CNF D4NNF\n", argv[0]);
	exit(0);
    }
    cfile = fopen(argv[argi], "r");
    if (cfile == NULL) {
	fprintf(stderr, "Can't open '%s'\n", argv[argi]);
	exit(1);
    }
    argi++;
    CNF cnf(cfile);
    fclose(cfile);
    if (cnf.failed()) {
	fprintf(stderr, "Aborted\n");
	exit(1);
    }
    Pog pog(&cnf);
    nfile = fopen(argv[argi], "r");
    if (nfile == NULL) {
	fprintf(stderr, "Can't open '%s'\n", argv[argi]);
	exit(1);
    }
    argi++;
    if (!pog.read_d4ddnnf(nfile)) {
	fprintf(stderr, "Error reading D4 NNF file\n");
	exit(1);
    }
    pog.show(stdout);
    return 0;
}
