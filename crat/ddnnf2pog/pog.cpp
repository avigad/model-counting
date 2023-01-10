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
#include <unordered_map>
#include "pog.hh"
#include "report.h"

// For use by the different routines
static Compressor compressor;

Pog_node::Pog_node() {
    type = POG_FALSE;
    degree = 0;
    children = NULL;
    split_var = 0;
    unit_id = 0;
}

Pog_node::Pog_node(pog_type_t ntype, int degree) {
    type = ntype;
    degree = degree;
    children = new int[degree];
    memset(children, 0, degree*sizeof(int));
    split_var = 0;
    unit_id = 0;
}

Pog_node::Pog_node(byte_vector_t &byte_rep) {
    degree = 0;
    children = NULL;
    split_var = 0;
    unit_id = 0;
    compressor.start_decompression(byte_rep.data());
    compressor.extract((int *) &type);
    if (type == POG_AND || type == POG_OR) {
	compressor.extract(&degree);
	children = new int[degree];
    }
    for (int i = 0; i < degree; i++) {
	compressor.extract(&children[i]);
    }
}

pog_type_t Pog_node::get_type() {
    return type;
}

void Pog_node::set_id(int i) {
    id = i;
}

int Pog_node::get_id() {
    return id;
}

void Pog_node::set_split_var(int var) {
    split_var = var;
}

int Pog_node::get_split_var() {
    return split_var;
}

void Pog_node::add_child(int index, int lit) {
    children[index] = lit;
}

void Pog_node::add_children2(int lit1, int lit2) {
    children[0] = lit1;
    children[1] = lit2;
}

int Pog_node::get_degree() {
    return degree;
}

int & Pog_node::operator[](int idx) {
    return children[idx];
}

void Pog_node::compress(byte_vector_t &bytes) {
    compressor.start_compression();
    compressor.add(type);
    if (type == POG_AND || type == POG_OR) {
	compressor.add(degree);
	for (int i = 0; i < degree; i++)
	    compressor.add(children[i]);
	compressor.emit(bytes);
    }
}

void Pog_node::show(FILE *outfile) {
    char nc = type == POG_AND ? 'P' : 'S';
    bool first = true;
    switch(type) {
    case POG_TRUE:
	fprintf(outfile, "TRUE");
	break;
    case POG_FALSE:
	fprintf(outfile, "FALSE");
	break;
    default:
	fprintf(outfile, "N%d_%c(", id, nc);
	for (int i = 0; i < degree; i++) {
	    fprintf(outfile, first ? "%d" : ",%d", children[i]);
	}
	fprintf(outfile, "\n");
    }
}


Pog::Pog() {
    cnf = NULL;
    max_input_var = 0;
}

Pog::Pog(CNF *cset) {
    cnf = cset;
    max_input_var = cset->max_variable();
}

int Pog::add_node(Pog_node *np) {
    nodes.push_back(np);
    int pid = max_input_var + nodes.size();
    np->set_id(pid);
    return pid;
}

void Pog::set_root_literal(int lit) {
    root_literal = lit;
}

int Pog::get_root() {
    return root_literal;
}

bool Pog::is_node(int lit) {
    int var = IABS(lit);
    return var > max_input_var && var <= max_input_var + nodes.size();
}

Pog_node * Pog::operator[](int id) {
    return nodes[id-max_input_var];
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

void Pog::mark(int rlit, int *markers) {
    if (is_node(rlit)) {
	int rid = IABS(rlit);
	int idx = rid-max_input_var;
	if (markers[idx])
	    return;
	markers[idx] = 1;
	Pog_node *np = (*this)[rid];
	for (int i = 0; i < np->get_degree(); i++)
	    mark((*np)[i], markers);
    }
}

bool Pog::optimize() {
    // If root represents input variable, then nothing need be done
    if (!is_node(root_literal)) {
	for (Pog_node *np : nodes)
	    delete np;
	nodes.resize(0);
	return true;
    }
    // Out of range IDs
    int vtrue = nodes.size() + max_input_var + 1;
    int vfalse = vtrue + 1;

    std::vector<Pog_node *> new_nodes;
    // Mapping from old id to new literal
    std::vector<int> remap;
    remap.resize(nodes.size());
    memset(remap.data(), 0, sizeof(int) * nodes.size());

    // Mark nodes that are reachable from root
    mark(root_literal, remap.data());

    // Skip inaccessible nodes and simplify operations
    for (int oid = max_input_var; oid < max_input_var + nodes.size(); oid++) {
	report(3, "Compressing POG with %d nodes and root literal %d\n", nodes.size(), root_literal);
	if (!remap[oid-max_input_var])
	    // Not reachable from root
	    continue;
	Pog_node *np = (*this)[oid];
	pog_type_t ntype = np->get_type();
	if (ntype == POG_TRUE)
	    remap[oid-max_input_var] = vtrue;
	else if (ntype == POG_FALSE)
	    remap[oid-max_input_var] = vfalse;
	else {
	    // AND or OR
	    std::vector<int> nchildren;
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		int cid = IABS(clit);
		if (is_node(clit)) {
		    int ncid = remap[cid];
		    if (ncid == vfalse || ncid == vtrue) {
			// Constant child.  Regularize value
			bool ctrue = clit < 0 ? ncid == vfalse : ncid == vtrue;
			if (ntype  == POG_AND && ctrue || ntype == POG_OR && !ctrue)
			    // Skip argument
			    continue;
			else if (ntype  == POG_AND && !ctrue || ntype == POG_OR && ctrue) {
			    const char *pname = ntype == POG_AND ? "AND" : "OR";
			    const char *cname = ctrue ? "TRUE" : "FALSE";
			    err(false, "Cannot handle Node #%d of type %s having child %d of type %s\n", 
				np->get_id(), pname, i, cname);
			    return false;
			}
		    } else
			nchildren.push_back(MATCH_PHASE(ncid, clit));
		} else
		    // Input literal
		    nchildren.push_back(clit);
	    }
	    if (nchildren.size() == 0)
		remap[oid-max_input_var] = ntype == POG_AND ? vtrue : vfalse;
	    else if (nchildren.size() == 1)
		remap[oid-max_input_var] = nchildren[0];
	    else {
		int ndegree = nchildren.size();
		Pog_node *nnp = new Pog_node(ntype, ndegree);
		for (int i = 0; i < ndegree; i++)
		    nnp->add_child(i, nchildren[i]);
		nnp->set_split_var(np->get_split_var());
		new_nodes.push_back(nnp);
		int nid = max_input_var + new_nodes.size();
		nnp->set_id(nid);
		remap[oid-max_input_var] = nid;
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
    // Degenerate cases:
    int rvar = IABS(root_literal);
    int nrvar = remap[rvar];
    // Clear out old nodes
    for (Pog_node *np : nodes)
	delete np;
    nodes.resize(0);
    if (nrvar == vfalse || nrvar == vtrue) {
	Pog_node *nnp = new Pog_node();
	add_node(nnp);
	nrvar = vfalse ? 1 : -1;
    } else if (IABS(nrvar) <= max_input_var) {
	// Input literal
	root_literal = MATCH_PHASE(nrvar, root_literal);
    } else {
	// Normal case.  Copy new nodes
	for (Pog_node *np : new_nodes)
	    add_node(np);
    }
    root_literal = MATCH_PHASE(nrvar, root_literal);
    report(3, "Compressed POG has %d nodes and root literal %d\n", nodes.size(), root_literal);
    return true;
}
    

