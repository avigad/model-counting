/*========================================================================
  Copyright (c) 2022, 2023 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
  ========================================================================*/


#include <stdlib.h>
#include <string.h>
#include <map>
#include <unordered_map>
#include <ctype.h>
#include "pog.hh"
#include "report.h"
#include "counters.h"

const char *pog_type_name[5] = { "NONE", "TRUE", "FALSE", "AND", "OR" };

const char pog_type_char[5] = { '\0', 't', 'f', 'a', 'o' };

Pog_node::Pog_node() {
    type = POG_TRUE;
    xvar = 0;
    degree = 0;
    children = NULL;
}

Pog_node::Pog_node(pog_type_t ntype) {
    type = ntype;
    xvar = 0;
    degree = 0;
    children = NULL;
    if (type == POG_AND || type == POG_AND)
	incr_count(COUNT_POG_AND);
    if (type == POG_OR)
	incr_count(COUNT_POG_OR);
}

Pog_node::~Pog_node() {
    if (degree > 0) delete children;
    if (type == POG_AND || type == POG_TRUE)
	incr_count_by(COUNT_POG_AND, -1);
    if (type == POG_OR)
	incr_count_by(COUNT_POG_OR, -1);
}

void Pog_node::set_type(pog_type_t t) {
    type = t;
}


pog_type_t Pog_node::get_type() {
    return type;
}

void Pog_node::set_xvar(int var) {
    xvar = var;
}

int Pog_node::get_xvar() {
    return xvar;
}

void Pog_node::set_defining_cid(int cid) {
    defining_cid = cid;
}

int Pog_node::get_defining_cid() {
    return defining_cid;
}


void Pog_node::add_children(std::vector<int> *cvec) {
    degree = cvec->size();
    if (degree > 0) {
	children = new int[degree];
	memcpy(children, cvec->data(), degree * sizeof(int));
    }
}

int Pog_node::get_degree() {
    return degree;
}

int & Pog_node::operator[](int idx) {
    return children[idx];
}

void Pog_node::show(FILE *outfile) {
    bool first = true;
    fprintf(outfile, "N%d_%s(", xvar, pog_type_name[type]);
    for (int i = 0; i < degree; i++) {
	fprintf(outfile, first ? "%d" : ",%d", children[i]);
	first = false;
    }
    fprintf(outfile, ")");
}

Pog::Pog() {
    cnf = NULL;
    max_input_var = 0;
}

Pog::Pog(Cnf_reasoner *cset) {
    cnf = cset;
    max_input_var = cset->max_variable();
}

int Pog::add_node(Pog_node *np) {
    nodes.push_back(np);
    int xvar = cnf->new_xvar();
    np->set_xvar(xvar);
    return xvar;
}

void Pog::set_root(int lit) {
    root_literal = lit;
}

int Pog::get_root() {
    return root_literal;
}

bool Pog::is_node(int lit) {
    int var = IABS(lit);
    return var > max_input_var && var <= max_input_var + nodes.size();
}

Pog_node * Pog::get_node(int id) {
    return nodes[id-max_input_var-1];
}

Pog_node * Pog::operator[](int id) {
    return nodes[id-max_input_var-1];
}

int Pog::node_count() {
    return nodes.size();
}

void Pog::show(FILE *outfile) {
    for (Pog_node *np : nodes) {
	np->show(outfile);
	fprintf(outfile, "\n");
    }
    fprintf(outfile, "ROOT %d\n", root_literal);
}

void Pog::topo_order(int rlit, std::vector<int> &rtopo, int *markers) {
    if (is_node(rlit)) {
	int rid = IABS(rlit);
	int idx = rid-max_input_var-1;
	if (markers[idx])
	    return;
	markers[idx] = 1;
	Pog_node *np = get_node(rid);
	for (int i = 0; i < np->get_degree(); i++)
	    topo_order((*np)[i], rtopo, markers);
	rtopo.push_back(rid);
    }
}

bool Pog::optimize() {
    if (verblevel >= 5) {
	printf("Before optimization:\n");
	show(stdout);
    }

    // If root represents input variable, then nothing need be done
    if (!is_node(root_literal)) {
	for (Pog_node *np : nodes)
	    delete np;
	nodes.resize(0);
	return true;
    }
    std::vector<Pog_node *> new_nodes;
    // Mapping from old id to new literal
    // Possibly create node for Boolean true
    // Create placeholder value for its use
    //    Pog_node *true_np = new Pog_node(POG_TRUE);
    //    new_nodes.push_back(true_np);
    //    int true_id = max_input_var + new_nodes.size();
    int true_id = max_input_var + nodes.size() + 1;
    cnf->reset_xvar();

    std::vector<int> remap;
    remap.resize(nodes.size(), 0);
    // Order old nodes in reverse topological order
    std::vector<int> rtopo;

    // Get topological ordering of nodes accessible from root
    topo_order(root_literal, rtopo, remap.data());

    report(2, "Compressing POG with %d nodes and root literal %d\n", nodes.size(), root_literal);
    // Process nodes in reverse topological order
    // Skip inaccessible nodes and simplify operations
    for (int oid : rtopo) {
	if (!remap[oid-max_input_var-1])
	    // Not reachable from root
	    continue;
	Pog_node *np = get_node(oid);
	pog_type_t ntype = np->get_type();
	if (ntype == POG_TRUE) 
	    remap[oid-max_input_var-1] = true_id;
	else if (ntype == POG_FALSE)
	    remap[oid-max_input_var-1] = -true_id;
	else if (ntype == POG_OR) {
	    if (np->get_degree() == 1) {
		int child_lit = (*np)[0];
		int nchild_lit = child_lit;
		if (is_node(child_lit)) {
		    int child_id = IABS(child_lit);
		    nchild_lit = MATCH_PHASE(remap[child_id-max_input_var-1], child_lit);
		}
		remap[oid-max_input_var-1] = nchild_lit;
		continue;
	    }
	    std::vector<int> nchildren;
	    // In case have only one non-false child
	    Pog_node *pcnp = NULL;
	    for (int i = 0; i < np->get_degree(); i++) {
		int child_lit = (*np)[i];
		int nchild_lit = child_lit;
		if (is_node(child_lit)) {
		    int child_id = IABS(child_lit);
		    nchild_lit = MATCH_PHASE(remap[child_id-max_input_var-1], child_lit);
		}
		if (is_node(nchild_lit) && nchild_lit > 0) {
		    Pog_node *cnp = new_nodes[nchild_lit-max_input_var-1];
		    if (cnp->get_type() == POG_AND) {
			pcnp = cnp;
		    }
		}
		nchildren.push_back(nchild_lit);
	    }
	    // If one of the children is true, then replace this node with other child
	    if ((nchildren[0] == -true_id || nchildren[1] == -true_id) && pcnp != NULL) {
		remap[oid-max_input_var-1] = pcnp->get_xvar();
		if (verblevel >= 4) {
		    printf("  Node ");
		    np->show(stdout);
		    printf("  maps to ");
		    pcnp->show(stdout);
		    printf("\n");
		}
		continue;
	    } else {
		Pog_node *nnp = new Pog_node(POG_OR);
		nnp->add_children(&nchildren);
		new_nodes.push_back(nnp);
		int nid = max_input_var + new_nodes.size();
		nnp->set_xvar(nid);
		remap[oid-max_input_var-1] = nid;
		if (verblevel >= 4) {
		    printf("  Converted node ");
		    np->show(stdout);
		    printf(" to ");
		    nnp->show(stdout);
		    printf("\n");
		}
	    }
	} else {
	    // AND
	    std::vector<int> nchildren;
	    bool zeroed = false;
	    for (int i = 0; i < np->get_degree(); i++) {
		int child_lit = (*np)[i];
		if (is_node(child_lit)) {
		    int child_id = IABS(child_lit);
		    int nchild_lit = MATCH_PHASE(remap[child_id-max_input_var-1], child_lit);
		    if (nchild_lit == true_id)
			// Skip child
			continue;
		    else if (nchild_lit == -true_id) {
			// Zero node
			remap[oid-max_input_var-1] = -true_id;
			if (verblevel >= 4) {
			    printf("  Converted node ");
			    np->show(stdout);
			    printf(" to FALSE\n");
			}
			zeroed = true;
			break;
		    } else
			nchildren.push_back(nchild_lit);
		} else
		    // Input literal
		    nchildren.push_back(child_lit);
	    }
	    if (zeroed)
		continue;
	    else if (nchildren.size() == 0) {
		err(true, "Translation of And node #%d has no children\n", oid);
		//		remap[oid-max_input_var-1] = -true_id;
	    } else if (nchildren.size() == 1)
		remap[oid-max_input_var-1] = nchildren[0];
	    else {
		Pog_node *nnp = new Pog_node(POG_AND);
		nnp->add_children(&nchildren);
		new_nodes.push_back(nnp);
		int nid = max_input_var + new_nodes.size();
		nnp->set_xvar(nid);
		remap[oid-max_input_var-1] = nid;
		if (verblevel >= 4) {
		    printf("  Converted node ");
		    np->show(stdout);
		    printf(" to ");
		    nnp->show(stdout);
		    printf("\n");
		}
	    }
	}
    }
    // Clear out old nodes
    for (Pog_node *np : nodes)
	delete np;
    nodes.resize(0);

    // Figure out root
    int rvar = IABS(root_literal);
    root_literal = MATCH_PHASE(remap[rvar-max_input_var-1], root_literal);
    int nrvar = IABS(root_literal);
    if (nrvar == true_id) {
	Pog_node *nnp = new Pog_node(POG_TRUE);
	add_node(nnp);
	root_literal = MATCH_PHASE(1, root_literal);
    } else if (IABS(nrvar) > max_input_var) {
	// Normal case.  Copy new nodes
	for (Pog_node *np : new_nodes)
	    add_node(np);
    }
    report(2, "Compressed POG has %d nodes and root literal %d\n", nodes.size(), root_literal);
    return true;
}
    

bool Pog::concretize() {
    if (verblevel >= 5) {
	printf("Before concretizing:\n");
	show(stdout);
    }

    if (verblevel >= 2) {
	// Document input clauses
	cnf->pwriter->comment("Input clauses");
	for (int cid = 1; cid <= cnf->clause_count(); cid++)
	    cnf->document_input(cid);
    }

    for (Pog_node *np : nodes) {
	ilist args = ilist_copy_list(&(*np)[0], np->get_degree());
	int xvar = np->get_xvar();
	int defining_cid = 0;
	bool need_zero = false;
	switch (np->get_type()) {
	case POG_TRUE:
	case POG_AND:
	    defining_cid = cnf->start_and(xvar, args);
	    need_zero = false;
	    break;
	case POG_OR:
	    need_zero = true;
	    defining_cid = cnf->start_or(xvar, args);
	    for (int i = 0; i < np->get_degree(); i++) {
		// Find mutual exclusions
		int child_lit = (*np)[i];
		if (is_node(child_lit)) {
		    Pog_node *cnp = get_node(child_lit);
		    int hid = cnp->get_defining_cid() + 1;
		    cnf->add_hint(hid);
		}
	    }
	    break;
	default:
	    err(true, "POG Node #%d.  Can't handle node type with value %d\n", np->get_xvar(), (int) np->get_type());
	}
	cnf->finish_command(need_zero);
	np->set_defining_cid(defining_cid);
	if (np->get_type() == POG_OR)
	    cnf->document_or(defining_cid, xvar, args);
	else
	    cnf->document_and(defining_cid, xvar, args);
	ilist_free(args);
	
    }
    return true;
}


// Try to read single alphabetic character from line
// If not found, then push back unread character and return 0
// If hit EOF, then return this
static int get_token(FILE *infile) {
    int c;
    while (true) {
	c = fgetc(infile);
	if (isalpha(c) || c == EOF)
	    return c;
	else if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    return 0;
	}
    }
}

// Read sequence of numbers from line of input
// Consume end of line character
// Return false if non-numeric value encountered
static bool read_numbers(FILE *infile, std::vector<int> &vec, int *rc) {
    vec.resize(0);
    while (true) {
	int c = fgetc(infile);
	int val;
	if (c == '\n' || c == EOF) {
	    *rc = c;
	    return true;
	} else if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    if (fscanf(infile, "%d", &val) == 1) {
		vec.push_back(val);
	    } else
		return false;
	}
    }
    // Won't hit this
    return false;
}


bool Pog::read_d4ddnnf(FILE *infile) {
    // Mapping from NNF ID to POG Node ID
    std::map<int,int> nnf_idmap;
    // Vector of arguments for each POG node
    std::vector<std::vector<int> *> arguments;
    // Capture arguments for each line
    std::vector<int> largs;
    int line_number = 0;
    // Statistics
    int nnf_node_count = 0;
    int nnf_explicit_node_count = 0;
    int nnf_edge_count = 0;
    while (true) {
	pog_type_t ntype = POG_NONE;
	line_number++;
	int c = get_token(infile);
	int rc = 0;
	if (c == EOF)
	    break;
	if (c != 0) {
	    for (int t = POG_TRUE; t <= POG_OR; t++)
		if (c == pog_type_char[t])
		    ntype = (pog_type_t) t;
	    if (ntype == POG_NONE)
		err(true, "Line #%d.  Unknown D4 NNF command '%c'\n", line_number, c);
	    nnf_node_count++;
	    nnf_explicit_node_count++;
	    Pog_node *np = new Pog_node(ntype);
	    int pid = add_node(np);
	    arguments.push_back(new std::vector<int>);
	    bool ok = read_numbers(infile, largs, &rc);
	    if (!ok)
		err(true, "Line #%d.  Couldn't parse numbers\n", line_number);
	    else if (largs.size() == 0 && rc == EOF)
		break;
	    else if (largs.size() != 2)
		err(true, "Line #%d.  Expected 2 numbers.  Found %d\n", line_number, largs.size());
	    else if (largs.back() != 0)
		err(true, "Line #%d.  Line not zero-terminated\n", line_number);
	    else
		nnf_idmap[largs[0]] = pid;
	    report(3, "Line #%d.  Created POG %s Node %d from NNF node %d\n",
		   line_number, pog_type_name[ntype], pid, largs[0]); 
	} else {
	    nnf_edge_count++;
	    bool ok = read_numbers(infile, largs, &rc);
	    if (!ok)
		err(true, "Line #%d.  Couldn't parse numbers\n", line_number);
	    else if (largs.size() == 0 && rc == EOF)
		break;
	    else if (largs.size() < 3)
		err(true, "Line #%d.  Expected at least 3 numbers.  Found %d\n", line_number, largs.size());
	    else if (largs.back() != 0)
		err(true, "Line #%d.  Line not zero-terminated\n", line_number);
	    // Find parent
	    auto fid = nnf_idmap.find(largs[0]);
	    if (fid == nnf_idmap.end())
		err(true, "Line #%d.  Invalid NNF node Id %d\n", line_number, largs[0]);
	    int ppid = fid->second;
	    // Find second node
	    fid = nnf_idmap.find(largs[1]);
	    if (fid == nnf_idmap.end())
		err(true, "Line #%d.  Invalid NNF node Id %d\n", line_number, largs[1]);
	    int spid = fid->second;
	    int cpid = spid;
	    if (largs.size() > 3) {
		// Must construct AND node to hold literals
		nnf_node_count++;
		Pog_node *anp = new Pog_node(POG_AND);
		cpid = add_node(anp);
		std::vector<int> *aargs = new std::vector<int>;
		arguments.push_back(aargs);
		for (int i = 2; i < largs.size()-1; i++)
		    aargs->push_back(largs[i]);
		aargs->push_back(spid);
		report(3, "Line #%d. Created POG AND Node %d to hold literals between NNF nodes %d and %d\n",
		       line_number, cpid, largs[0], largs[1]); 
	    }
	    std::vector<int> *pargs = arguments[ppid-max_input_var-1];
	    pargs->push_back(cpid);
	    report(4, "Line #%d.  Adding edge between POG nodes %d and %d\n", line_number, ppid, cpid);
	}
    }
    // Add arguments
    for (int pid = max_input_var + 1; pid <= max_input_var + nodes.size(); pid++) {
	Pog_node *np = get_node(pid);
	std::vector<int> *args = arguments[pid-max_input_var-1];
	np->add_children(args);
	delete args;
    }
    for (auto kv : nnf_idmap) {
	int nid = kv.first;
	int pid = kv.second;
	Pog_node *np = get_node(pid);
	// Check OR nodes
	if (np->get_type() == POG_OR) {
	    int degree = np->get_degree();
	    if (degree == 0 || degree > 2) 
		err(true, "NNF OR node %d.  Invalid degree %d\n", nid, degree);
	    else if (degree == 1) {
		root_literal = pid;
		report(3, "Setting root literal to %d\n", root_literal);
	    }
	}
    }
    report(1, "Read D4 NNF file with %d nodes (%d explicit) and %d edges\n",
	   nnf_node_count, nnf_explicit_node_count, nnf_edge_count);
    if (!optimize())
	return false;
    return (concretize());
}

// Recursively descend Pog until find input literal
int Pog::first_literal(int rlit) {
    if (is_node(rlit)) {
	Pog_node *np = get_node(IABS(rlit));
	int clit = (*np)[0];
	return first_literal(clit);
    }
    return rlit;
}

// Justify each position in POG within current context
// Return ID of justifying clause
int Pog::justify(int rlit, bool parent_or) {
    int jcid = 0;
    if (is_node(rlit)) {
	int rvar = IABS(rlit);
	Pog_node *rnp = get_node(rvar);
	int xvar = rnp->get_xvar();
	Clause *jclause = new Clause();
	jclause->add(xvar);
	for (int alit : *cnf->get_assigned_literals())
	    jclause->add(-alit);
	std::vector<int> hints;
	cnf->new_context();
	bool documented = false;
	switch (rnp->get_type()) {
	case POG_OR:
	    {
		incr_count(COUNT_VISIT_OR);
		int clit[2];
		int jid;
		int lhints[2][2];
		int hcount[2] = {0,0};
		int jcount = 0;
		for (int i = 0; i < 2; i++) {
		    clit[i] = (*rnp)[i];
		    lhints[i][hcount[i]++] = rnp->get_defining_cid()+i+1;
		    jid = justify(clit[i], true);
		    if (jid > 0) {
			jcount++;
			lhints[i][hcount[i]++] = jid;
		    }
		}
		if (jcount > 1) {
		    // Must prove in two steps
		    int slit = first_literal(clit[0]);
		    Clause *jclause0 = new Clause();
		    jclause0->add(-slit);
		    jclause0->add(xvar);
		    for (int alit : *cnf->get_assigned_literals())
			jclause0->add(-alit);
		    cnf->pwriter->comment("Justify node N%d_%s", xvar, pog_type_name[rnp->get_type()]);
		    documented = true;
		    int cid0 = cnf->start_assertion(jclause0);
		    for (int h = 0; h < hcount[0]; h++)
			cnf->add_hint(lhints[0][h]);
		    cnf->finish_command(true);
		    incr_count(COUNT_OR_JUSTIFICATION_CLAUSE);
		    hints.push_back(cid0);
		    for (int h = 0; h < hcount[1]; h++)
			hints.push_back(lhints[1][h]);
		} else {
		    // Can do with single proof step
		    incr_count(COUNT_OR_JUSTIFICATION_CLAUSE);
		    for (int i = 0; i < 2; i++)
			for (int h = 0; h < hcount[i]; h++)
			    hints.push_back(lhints[i][h]);
		}
	    }
	    break;
	case POG_AND:
	    {
		incr_count(COUNT_VISIT_AND);
		int cnext = 0;
		// If parent is OR, first argument is splitting literal
		if (parent_or) {
		    int clit0 = (*rnp)[cnext++];
		    cnf->push_assigned_literal(clit0);
		    jclause->add(-clit0);
		}

		// Bundle up the literals and justify them with single call
		std::vector<int> lits;
		std::vector<int> jids;
		for (; cnext < rnp->get_degree(); cnext++) {
		    int clit = (*rnp)[cnext];
		    if (is_node(clit))
			break;
		    lits.push_back(clit);
		}
		if (lits.size() > 0) {
		    cnf->pwriter->comment("Justify node N%d_%s, starting with %d literals", xvar, pog_type_name[rnp->get_type()], lits.size());
		    documented = true;
		    report(4, "Justify node N%d_%s, starting with %d literals\n", xvar, pog_type_name[rnp->get_type()], lits.size());
		    cnf->validate_literals(lits, jids);
		    for (int jid : jids)
			hints.push_back(jid);
		}

		// Now deal with the node arguments
		bool partition = false;
		std::unordered_map<int,int> var2rvar;
		std::unordered_map<int,std::set<int>*> rvar2cset;
		std::set<int> *save_clauses = NULL;
		std::set<int> *pset = NULL;
		for (; cnext < rnp->get_degree(); cnext++) {
		    int clit = (*rnp)[cnext];
		    if (!partition && cnext < rnp->get_degree()-1 && is_node(clit)) {
			// Must partition clauses
			cnf->partition_clauses(var2rvar, rvar2cset);
			partition = true;
			save_clauses = new std::set<int>;
			cnf->extract_active_clauses(save_clauses);
			if (!documented) 
			    report(4, "Justifying node N%d.  Partitioned clauses into %d sets\n", xvar, rvar2cset.size());
			documented = true;
		    }
		    if (partition) {
			int llit = first_literal(clit);
			int rvar = var2rvar.find(IABS(llit))->second;
			pset = rvar2cset.find(rvar)->second;
			// Restrict clauses to those relevant to this partition
			cnf->set_active_clauses(pset);
		    } 
		    int jid = justify(clit, false);
		    hints.push_back(jid);
		    if (pset != NULL)
			delete pset;
		}
		hints.push_back(rnp->get_defining_cid());
		if (save_clauses != NULL)
		    cnf->set_active_clauses(save_clauses);
		incr_count(COUNT_AND_JUSTIFICATION_CLAUSE);
	    }
	    break;
	default:
	    err(true, "Unknown POG type %d\n", (int) rnp->get_type());
	}
	if (!documented)
	    cnf->pwriter->comment("Justify node N%d_%s", xvar, pog_type_name[rnp->get_type()]);
	jcid = cnf->start_assertion(jclause);
	for (int hint : hints)
	    cnf->add_hint(hint);
	cnf->finish_command(true);
	cnf->pop_context();
    } else if (!parent_or)
	jcid = cnf->validate_literal(rlit, Cnf_reasoner::MODE_FULL);
    if (jcid > 0)
	report(4, "Literal %d in POG justified by clause %d\n", rlit, jcid);
    return jcid;
}

// Objective: Prove that Pog cannot evalute to true for any input that doesn't satisfy the clause
// I.e., that pog node logically implies clause
void Pog::delete_input_clause(int cid, int unit_cid) {
    Clause *cp = cnf->get_input_clause(cid);

    // Label each node by whether or not it is guaranteed to imply the clause
    bool *implies_clause = new bool[nodes.size()];

    std::vector<int> *dvp = new std::vector<int>;
    dvp->push_back(cid);
    dvp->push_back(unit_cid);

    for (int nidx = 0; nidx < nodes.size(); nidx++) {
	Pog_node *np = nodes[nidx];
	bool implies = false;
	switch (np->get_type()) {
	case POG_AND:
	    implies = false;
	    // Must have at least one child implying the clause
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		if (is_node(clit)) {
		    if (clit <= 0)
			err(true, "Encountered invalid Pog identifier %d while deleting clause %d\n", clit, cid);
		    implies = implies_clause[clit-max_input_var-1];
		    if (implies) {
			dvp->push_back(np->get_defining_cid()+i+1);
			break;
		    }
		} else {
		    implies = cp->contains(clit);
		    if (implies) {
			dvp->push_back(np->get_defining_cid()+i+1);
			break;
		    }
		}
	    }
	    break;
	case POG_OR:
	    // Must have all children implying the clause
	    implies = true;
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		if (is_node(clit)) {
		    if (clit <= 0)
			err(true, "Encountered invalid Pog identifier %d while deleting clause %d\n", clit, cid);
		    implies &= implies_clause[clit-max_input_var-1];
		} else
		    implies &= cp->contains(clit);
	    }
	    if (implies)
		dvp->push_back(np->get_defining_cid());
	    break;
	default:
	    err(true, "Uknown POG type %d for node N%d\n", (int) np->get_type(), np->get_xvar());
	}
	implies_clause[nidx] = implies;	    
    }
    if (!implies_clause[nodes.size()-1])
	err(true, "Failed to generate deletion proof of clause %d for root node\n", cid);
    cnf->pwriter->clause_deletion(dvp);
    delete dvp;
    delete[] implies_clause;
}
