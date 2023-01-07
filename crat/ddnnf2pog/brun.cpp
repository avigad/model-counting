// Test unit propagation part of program

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "clause.hh"
#include "report.h"

int main(int argc, const char *argv[]) {
    int cid = 0;
    FILE *cfile = NULL;
    FILE *pfile = stdout;
    //    verblevel = 3;
    if (argc <= 1 || strcmp(argv[1], "-h") == 0) {
	printf("Usage: %s CNF (lit|.)*\n", argv[0]);
	exit(0);
    }
    cfile = fopen(argv[1], "r");
    if (cfile == NULL) {
	fprintf(stderr, "Can't open '%s'\n", argv[1]);
	exit(1);
    }
    CNF cnf(cfile);
    fclose(cfile);
    if (cnf.failed()) {
	fprintf(stderr, "Aborted\n");
	exit(1);
    }
    if (!cnf.enable_pog(pfile, &cid)) {
	exit(1);
    }
    for (int idx = 2; idx < argc; idx++) {
	if (strcmp(argv[idx], ".") == 0) {
	    printf("c Popping one level\n");
	    if (!cnf.pop_context(1))
		printf("c Conflict found\n");
	}
	else {
	    int lit = atoi(argv[idx]);
	    printf("c Asserting %d\n", lit);
	    if (!cnf.new_context(lit))
		printf("c Conflict found\n");
	}
    }

    return 0;
}
