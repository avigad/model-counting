#include <cstdio>
#include "project.hh"
#include "report.h"
#include "counters.h"

Project::Project(const char *cnf_name) {
    FILE *cnf_file = fopen(cnf_name, "r");
    if (!cnf_file) 
	err(true, "Couldn't open file '%s'\n", cnf_name);
    Cnf *cnf = new Cnf();
    cnf->import_file(cnf_file);
    if (!cnf->is_loaded())
	err(true, "Failed to load CNF from file '%s'\n", cnf_name);
    report(1, "CNF file loaded %d variables, %d clauses, %d show variables\n", cnf->variable_count(), cnf->clause_count(), cnf->show_variables.size());
    fmgr.set_root(cnf_name);
    cr = new Clausal_reasoner(cnf);
    pog = new Pog(cnf->variable_count());
    root_literal = compile();
    report(1, "Initial POG created.  %d node, %d edges  POG size %d  Root literal = %d\n", 
	   pog->node_count(), pog->edge_count(), pog->node_count() + pog->edge_count(),
	   root_literal);
}

Project::~Project() {
    delete cr;
    delete pog;
}

int Project::compile() {
    char cmd[200];
    const char *cnf_name = fmgr.build_name("cnf", true);
    const char *nnf_name = fmgr.build_name("nnf", false);
    double start = tod();
    FILE *cnf_file = fopen(cnf_name, "w");
    if (!cnf_file)
	err(true, "Couldn't open CNF file '%s'\n", cnf_name);
    cr->write(cnf_file);
    fclose(cnf_file);
    snprintf(cmd, 200, "d4 %s -dDNNF -out=%s > /dev/null", cnf_name, nnf_name);
    report(3, "Running '%s'\n", cmd);
    FILE *pipe = popen(cmd, "w");
    int rc = pclose(pipe);
    double elapsed = tod()-start;
    incr_timer(TIME_KC, elapsed);
    report(2, "Running D4 on %s required %.3f seconds.  Return code = %d\n", cnf_name, elapsed, rc);

    FILE *nnf_file = fopen(nnf_name, "r");
    if (!nnf_file)
	err(true, "Couldn't open NNF file '%s'\n", nnf_name);
    int root = pog->load_nnf(nnf_file);
    fclose(nnf_file);
    report(3, "Imported NNF file '%s'.  Root literal = %d\n", nnf_name, root);
    if (verblevel >= 4)
	pog->show(stdout);

    return root;
}
