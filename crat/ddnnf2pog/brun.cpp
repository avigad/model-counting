// Test unit propagation part of program

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "clause.hh"
#include "report.h"
#include "writer.hh"


int main(int argc, const char *argv[]) {
    int cid = 0;
    FILE *cfile = NULL;
    PogWriter pwriter;
    verblevel = 1;
    if (argc <= 1 || strcmp(argv[1], "-h") == 0) {
	printf("Usage: %s [VLEVEL] CNF (lit|.)*\n", argv[0]);
	exit(0);
    }
    int argi = 1;
    if (isdigit(*argv[argi])) {
	verblevel = atoi(argv[argi]);
	argi++;
    }
    if (argi >= argc) {
	printf("Usage: %s [VLEVEL] CNF (lit|.)*\n", argv[0]);
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
    if (!cnf.enable_pog(&pwriter)) {
	exit(1);
    }
    while (argi < argc) {
	if (strcmp(argv[argi], ".") == 0) {
 	    printf("c Popping one level\n");
	    cnf.pop_context();
	    if (!cnf.bcp())
		printf("c Conflict found\n");
	}
	else {
	    int lit = atoi(argv[argi]);
	    printf("c Asserting %d\n", lit);
	    cnf.new_context();
	    cnf.push_assigned_literal(lit);
	    if (!cnf.bcp())
		printf("c Conflict found\n");
	}
	argi++;
    }

    return 0;
}
