// Test unit propagation part of program

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
    Pog_writer pwriter;
    verblevel = 1;
    bool conflict_found = false;
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
    Cnf_reasoner cnf(cfile);
    fclose(cfile);
    if (cnf.failed()) {
	fprintf(stderr, "Aborted\n");
	exit(1);
    }
    if (!cnf.enable_pog(&pwriter)) {
	exit(1);
    }
    cnf.delete_files = false;
    std::unordered_map<int,int> var2rvar;
    std::unordered_map<int,std::set<int>*> rvar2cset;
    cnf.partition_clauses(var2rvar, rvar2cset);
    if (verblevel >= 2) {
	printf("Partitioning into disjoint clauses\n");
	for (auto fid : rvar2cset) {
	    printf("Reference variable %d:", fid.first);
	    std::set<int> *cset = fid.second;
	    for (int cid : *cset)
		printf(" %d", cid);
	    printf("\n");
	}
    }
    

    int depth = 0;
    while (argi < argc) {
	if (strcmp(argv[argi], ".") == 0) {
 	    printf("c Popping one level\n");
	    depth--;
	    if (depth < 0) {
		printf("Attempt to pop below depth 0\n");
		return 1;
	    }
	    cnf.pop_context();
	    int ncid = cnf.bcp(false);
	    if (ncid > 0) {
		conflict_found = true;
		printf("c Conflict found.  Clause %d\n", ncid);
	    }
	}
	else {
	    int lit = atoi(argv[argi]);
	    printf("c Pushing level and asserting %d\n", lit);
	    cnf.new_context();
	    depth++;
	    cnf.push_assigned_literal(lit);
	    int ncid = cnf.bcp(false);
	    if (ncid > 0) {
		conflict_found = true;
		printf("c Conflict found.  Clause %d\n", ncid);
	    }
	}
	argi++;
    }

    if (depth > 0) {
	printf("c Stopped at depth %d\n", depth);
	return 0;
    }

    if (!cnf.is_unsatisfiable()) {
	// Extract reduced CNF representation
	Cnf_reduced *rcp = cnf.extract_cnf();
	rcp->run_solver();
	while (true) {
	    std::vector<int> *context = cnf.get_assigned_literals();
	    Clause *pnp = rcp->get_proof_clause(context);
	    if (pnp == NULL)
		break;
	    int ncid = cnf.rup_validate(pnp);
	    if (ncid == 0) {
		err(false, "Failed to validate proof clause\n");
		pnp->show();
	    }
	}
	delete rcp;
    }

    return 0;
}
