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
    std::unordered_map<int,int> var2rvar;
    std::unordered_map<int,std::vector<int>*> rvar2clist;
    cnf.partition_clauses(var2rvar, rvar2clist);
    if (verblevel >= 2) {
	printf("Partitioning into disjoint clauses\n");
	for (auto fid : rvar2clist) {
	    printf("Reference variable %d:", fid.first);
	    std::vector<int> *cvec = fid.second;
	    for (int cid : *cvec)
		printf(" %d", cid);
	    printf("\n");
	}
    }
    

    while (argi < argc) {
	if (strcmp(argv[argi], ".") == 0) {
 	    printf("c Popping one level\n");
	    cnf.pop_context();
	    if (!cnf.bcp()) {
		conflict_found = true;
		printf("c Conflict found\n");
	    }
	}
	else {
	    int lit = atoi(argv[argi]);
	    printf("c Asserting %d\n", lit);
	    cnf.new_context();
	    cnf.push_assigned_literal(lit);
	    if (!cnf.bcp()) {
		conflict_found = true;
		printf("c Conflict found\n");
	    }
	}
	argi++;
    }
    // Extract reduced CNF representation
    Cnf_reduced *rcp = cnf.extract_cnf();
    rcp->run_solver();
    while (true) {
	std::vector<int> *context = cnf.get_assigned_literals();
	Clause *pnp = rcp->get_proof_clause(context);
	if (pnp == NULL)
	    break;
	bool ok = cnf.rup_validate(pnp);
	if (!ok) {
	    err(false, "Failed to validate proof clause\n");
	    pnp->show();
	}
    }
    delete rcp;

    // Attempt final step in UNSAT proof
    Clause *tcp = new Clause();
    bool ok = cnf.rup_validate(tcp);
    if (!ok) {
	err(false, "Failed to finish UNSAT proof\n");
    }
    

    return 0;
}
