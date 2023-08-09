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
    fclose(cnf_file);
    if (!cnf->is_loaded())
	err(true, "Failed to load CNF from file '%s'\n", cnf_name);
    report(1, "CNF file loaded %d variables, %d clauses, %d data variables\n", cnf->variable_count(), cnf->clause_count(), cnf->data_variables.size());
    fmgr.set_root(cnf_name);
    cr = new Clausal_reasoner(cnf);
    cr->bcp(false);
    pog = new Pog(cnf->variable_count());
    root_literal = compile();
    report(1, "Initial POG created.  %d node, %d edges  POG size %d  Root literal = %d\n", 
	   pog->node_count(), pog->edge_count(), pog->node_count() + pog->edge_count(),
	   root_literal);
    incr_count_by(COUNT_POG_INITIAL_SUM, get_count(COUNT_POG_SUM));
    incr_count_by(COUNT_POG_INITIAL_PRODUCT, get_count(COUNT_POG_PRODUCT));
    incr_count_by(COUNT_POG_INITIAL_EDGES, get_count(COUNT_POG_EDGES));
    incr_timer(TIME_INITIAL_KC, get_timer(TIME_KC));
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
    report(4, "Running '%s'\n", cmd);
    FILE *pipe = popen(cmd, "w");
    int rc = pclose(pipe);
    double elapsed = tod()-start;
    incr_timer(TIME_KC, elapsed);
    incr_count(COUNT_KC_CALL);
    incr_histo(HISTO_KC_CLAUSES, cr->current_clause_count());
    report(3, "Running D4 on %s required %.3f seconds.  Return code = %d\n", cnf_name, elapsed, rc);

    FILE *nnf_file = fopen(nnf_name, "r");
    if (!nnf_file)
	err(true, "Couldn't open NNF file '%s'\n", nnf_name);
    int osize = pog->node_count();
    int root = pog->load_nnf(nnf_file);
    int dsize = pog->node_count() - osize;
    fclose(nnf_file);
    report(4, "Imported NNF file '%s'.  Root literal = %d.  Added %d nodes\n", nnf_name, root, dsize);
    if (verblevel >= 5)
	pog->show(root, stdout);
    incr_histo(HISTO_POG_NODES, dsize);
    return root;
}

void Project::projecting_compile() {
    cr->bcp(false);
    root_literal = traverse(root_literal);
}

bool Project::write(const char *pog_name) {
    FILE *pog_file = fopen(pog_name, "w");
    if (!pog_file)
	err(true, "Couldn't open file '%s'\n", pog_name);
    bool ok = pog->write(root_literal, pog_file);
    fclose(pog_file);
    return ok;
}

int Project::traverse(int edge) {
    // Terminal conditions
    if (pog->is_node(edge)) {
	return pog->get_type(edge) == POG_SUM ? traverse_sum(edge) : traverse_product(edge);
    } else if (cr->is_data_variable(pog->get_var(edge)))
	return edge;
    else
	return TAUTOLOGY;
}

int Project::traverse_sum(int edge) {
    int edge1 = pog->get_argument(edge, 0);
    int nedge1 = traverse(edge1);
    int edge2 = pog->get_argument(edge, 1);
    int nedge2 = traverse(edge2);
    int dvar = pog->get_decision_variable(edge);
    int nedge = 0;
    const char *descr = "";
    if (!cr->is_data_variable(dvar)) {
	cr->new_context();
	cr->quantify(dvar);
	cr->bcp(false);
	if (cr->is_satisfiable()) {
	    int uroot = compile();
	    int xroot = traverse(uroot);
	    pog->start_node(POG_SUM);
	    pog->add_argument(-nedge1);
	    pog->add_argument(xroot);
	    int mroot = pog->finish_node();
	    pog->start_node(POG_SUM);
	    pog->add_argument(-mroot);
	    pog->add_argument(nedge2);
	    nedge = pog->finish_node();
	    descr = "excluding";
	    incr_count(COUNT_VISIT_EXCLUDING_SUM);
	} else {
	    descr = "mutex";
	    incr_count(COUNT_VISIT_MUTEX_SUM);
	}
	cr->pop_context();
    } else {
	descr = "data";
	incr_count(COUNT_VISIT_DATA_SUM);
    }
    if (nedge == 0) {
	pog->start_node(POG_SUM);
	pog->add_argument(nedge1);
	pog->add_argument(nedge2);
	nedge = pog->finish_node();
    }
    report(5, "Traversal of Sum node %d yielded edge %d.  Sum type = %s\n", edge, nedge, descr);
    return nedge;
}

int Project::traverse_product(int edge) {
    cr->new_context();
    int degree = pog->get_degree(edge);
    std::vector<int> nargs;
    std::vector<int> cedges;
    for (int i = 0; i < degree; i++) {
	int cedge = pog->get_argument(edge, i);
	int cvar = pog->get_var(cedge);
	if (pog->is_node(cedge))
	    cedges.push_back(cedge);
	else {
	    cr->assign_literal(cedge, false);
	    if (cr->is_data_variable(cvar))
		nargs.push_back(cedge);
	}
    }
    if (cedges.size() > 0) {
	cr->bcp(true);
	if (cedges.size() == 1) 
	    nargs.push_back(traverse(cedges[0]));
	else {
	    std::unordered_set<int> vset;
	    for (int cedge : cedges) {
		cr->new_context();
		vset.clear();
		pog->get_variables(cedge, vset);
		cr->partition(vset);
		nargs.push_back(traverse(cedge));
		cr->pop_context();
	    }
	}
    }
    cr->pop_context();
    pog->start_node(POG_PRODUCT);
    for (int cedge : nargs)
	pog->add_argument(cedge);
    int nedge = pog->finish_node();
    report(5, "Traversal of Product node %d yielded edge %d.\n", edge, nedge);
    incr_count(COUNT_VISIT_PRODUCT);
    return nedge;
}
