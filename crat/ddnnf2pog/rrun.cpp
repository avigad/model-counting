// Test RUP proof capabilities
// Convert sequence of clauses into sequence of hinted assertions
// Proof file given in CNF, complete with header

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "clausal.hh"
#include "report.h"
#include "writer.hh"


int main(int argc, const char *argv[]) {
    int cid = 0;
    FILE *cfile = NULL;
    FILE *dfile = NULL;
    Pog_writer pwriter;
    verblevel = 1;
    if (argc <= 1 || strcmp(argv[1], "-h") == 0) {
	printf("Usage: %s [VLEVEL] CNF DRAT\n", argv[0]);
	exit(0);
    }
    int argi = 1;
    if (isdigit(*argv[argi])) {
	verblevel = atoi(argv[argi]);
	argi++;
    }
    if (argi+1 >= argc) {
	printf("Usage: %s [VLEVEL] CNF DRAT\n", argv[0]);
	exit(0);
    }
    cfile = fopen(argv[argi], "r");
    if (cfile == NULL) {
	fprintf(stderr, "Can't open '%s'\n", argv[argi]);
	exit(1);
    }
    argi++;
    Cnf_reasoner cnf(cfile);
    fclose(cfile);
    if (cnf.failed()) {
	fprintf(stderr, "Aborted\n");
	exit(1);
    }
    if (!cnf.enable_pog(&pwriter)) {
	exit(1);
    }

    dfile = fopen(argv[argi], "r");
    if (dfile == NULL) {
	fprintf(stderr, "Can't open '%s'\n", argv[argi]);
	exit(1);
    }
    Cnf proof(dfile);
    if (proof.failed()) {
	fprintf(stderr, "Aborted\n");
	exit(1);
    } else if (verblevel >= 3) {
	report(3, "Proof clauses:\n");
	proof.show();
    }
    bool conflict = false;
    for (int pid = 1; pid <= proof.clause_count(); pid++) {
	Clause *clp = proof[pid]; 
	if (!cnf.rup_validate(clp)) {
	    fprintf(stderr, "Failed\n");
	    exit(1);
	}
	if (clp->length() == 0)
	    conflict = true;
    }
    if (conflict)
	fprintf(stderr, "c VALIDATED\n");
    else
	fprintf(stderr, "c No conflict found.  NOT validated\n");
    return 0;
}
