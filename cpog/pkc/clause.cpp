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

#include <cstdlib>
#include <cstdio>
#include <ctype.h>
#include <cstring>
#include "clause.hh"
#include "report.h"
#include "counters.h"

static int skip_line(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return c;
    }
    return c;
}

// Skip over comment lines, spaces, newlines, etc., until find something interesting
// Return false if EOF encountered without finding anything
static bool find_token(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == 'c') {
	    c = skip_line(infile);
	    ungetc(c, infile);
	} else if (!isspace(c)) {
	    ungetc(c, infile);
	    return true;
	}
	// Skip space
    }
    return false;
}

// Tools to enable constructing CNF representations
static void start_build(std::vector<int> &varx, int nvar, int nclause) {
    varx.push_back(nvar);
    varx.push_back(nclause);
    for (int cid = 1; cid <= nclause+1; cid++)
	// Place holder for starting indices
	varx.push_back(0);
}

static void new_clause(std::vector<int> &varx, int cid) {
    varx[cid+1] = varx.size();
}

static void add_literal(std::vector<int> &varx, int lit) {
    varx.push_back(lit);
}

static cnf_archive_t finish_build(std::vector<int> &varx) {
    int nclause = varx[1];
    varx[nclause+2] = varx.size();
    cnf_archive_t arx = (cnf_archive_t) calloc(varx.size(), sizeof(int));
    if (!arx) {
	err(false, "Couldn't allocate space for clauses\n");
	arx = NULL;
	return NULL;
    }
    memcpy(arx, varx.data(), varx.size() * sizeof(int));
    return arx;
}


Cnf::Cnf() {
    arx = NULL;
}

void Cnf::import_file(FILE *infile) { 
    int expectedNvar = 0;
    int expectedNclause = 0;
    int nclause = 0;
    bool read_failed = false;
    bool got_header = false;
    int c;
    if (arx) {
	free(arx);
	arx = NULL;
    }
    std::vector<int> varx;
    bool eof = false;
    // Look for CNF header
    while ((c = getc(infile)) != EOF) {
	if (isspace(c)) 
	    continue;
	if (c == 'c')
	    c = skip_line(infile);
	if (c == EOF) {
	    err(false, "Not valid CNF file.  No header line found\n");
	    return;
	}
	if (c == 'p') {
	    char field[20];
	    if (fscanf(infile, "%s", field) != 1) {
		err(false, "Not valid CNF file.  Invalid header line\n");
		return;
	    }
	    if (strcmp(field, "cnf") != 0) {
		err(false, "Not valid CNF file.  Header line shows type is '%s'\n", field);
		return;
	    }
	    if (fscanf(infile, "%d %d", &expectedNvar, &expectedNclause) != 2) {
		err(false, "Invalid CNF header\n");
		return;
	    } 
	    start_build(varx, expectedNvar, expectedNclause);
	    c = skip_line(infile);
	    got_header = true;
	    break;
	}
	if (c == EOF) {
	    err(false, "Invalid CNF.  EOF encountered before reading any clauses\n");
	    return;
	}
    }
    if (!got_header) {
	err(false, "Not valid CNF.  No header line found\n");
	return;
    }
    while (nclause < expectedNclause) {
	// Setup next clause
	nclause++;
	new_clause(varx, nclause);
	while (true) {
	    eof = !find_token(infile);
	    int lit;
	    if (eof) {
		err(false, "Unexpected end of file\n");
		return;
	    }
	    if (fscanf(infile, "%d", &lit) != 1) {
		err(false, "Couldn't find literal or 0\n");
		return;
	    }
	    if (lit == 0)
		break;
	    else 
		add_literal(varx, lit);
	}
    }	
    arx = finish_build(varx);
    incr_count_by(COUNT_INPUT_CLAUSE, clause_count());
    incr_count_by(COUNT_INPUT_VAR, variable_count());
}

void Cnf::import_archive(cnf_archive_t iarx) {
    arx = iarx;
}

Cnf::~Cnf() {
    arx = NULL;
}

void Cnf::deallocate() {
    if (arx != NULL)
	free(arx);
    arx = NULL;
}

int Cnf::variable_count() {
    return arx ? arx[0] : 0;
}

int Cnf::clause_count() {
    return arx ? arx[1] : 0;
}

int Cnf::clause_length(int cid) {
    if (!arx)
	return 0;
    if (cid < 1 || cid > clause_count())
	err(true, "Invalid clause ID: %d\n", cid);
    return arx[cid+2] - arx[cid+1];
}

int Cnf::get_literal(int cid, int lid) {
    if (!arx)
	return 0;
    int len = clause_length(cid);
    int offset = arx[cid+1];
    if (lid >= 0 && lid < len)
	return arx[offset+lid];
    else
	err(true, "Invalid literal index %d for clause #%d.  Clause length = %d\n", lid, cid, len);
    return 0;
}

bool Cnf::show(FILE *outfile) {
#if 0
    int full_length = arx[clause_count() + 2];
    fprintf(outfile, "Raw data (%d arx):", full_length);
    for (int i = 0; i < full_length; i++)
	fprintf(outfile, " %d", arx[i]);
    fprintf(outfile, "\n");
#endif

    int ccount = clause_count();
    for (int cid = 1; cid <= ccount; cid++) {
	int len = clause_length(cid);
	fprintf(outfile, "%d:", cid);
	for (int lid = 0; lid < len; lid++)
	    fprintf(outfile, " %d", get_literal(cid, lid));
	fprintf(outfile, "\n");
    }
    return true;
}

bool Cnf::write(FILE *outfile) {
    int nvar = variable_count();
    int ccount = clause_count();
    fprintf(outfile, "p cnf %d %d\n", nvar, ccount);
    for (int cid = 1; cid <= ccount; cid++) {
	int len = clause_length(cid);
	for (int lid = 0; lid < len; lid++)
	    fprintf(outfile, "%d ", get_literal(cid, lid));
	fprintf(outfile, "0\n");
    }
    return true;
}

Clausal_reasoner::Clausal_reasoner(Cnf *icnf) {
    cnf = icnf;
    // Set up active clauses
    curr_active_clauses = new std::set<int>;
    next_active_clauses = new std::set<int>;
    for (int cid = 1; cid <= cnf->clause_count(); cid++)
	curr_active_clauses->insert(cid);
    new_context();
}

Clausal_reasoner::~Clausal_reasoner() {
    delete curr_active_clauses;
    delete next_active_clauses;
}

void Clausal_reasoner::new_context() {
    unit_trail.push_back(0);
    uquant_trail.push_back(0);
    deactivated_clauses.push_back(0);
}

void Clausal_reasoner::pop_context() {
    while (true) {
	int lit = unit_trail.back();
	unit_trail.pop_back();
	if (lit == 0)
	    break;
	unit_literals.erase(lit);
    }
    while (true) {
	int var = uquant_trail.back();
	uquant_trail.pop_back();
	if (var ==  0)
	    break;
	quantified_variables.erase(var);
    }
    while (true) {
	int cid = deactivated_clauses.back();
	deactivated_clauses.pop_back();
	if (cid == 0)
	    break;
	curr_active_clauses->erase(cid);
    }
}

void Clausal_reasoner::deactivate_clause(int cid) {
    deactivated_clauses.push_back(cid);
}


void Clausal_reasoner::assign_literal(int lit) {
    int var = IABS(lit);
    if (unit_literals.find(lit) != unit_literals.end()) {
	err(false, "Attempt to assign literal %d that has already been assigned\n", lit);
    } else if (unit_literals.find(-lit) != unit_literals.end()) {
	err(false, "Attempt to assign literal %d for which its negation has already been assigned\n", lit);
    } else if (quantified_variables.find(var) != quantified_variables.end()) {
	err(false, "Attempt to assign literal %d even though variable quantified\n", lit);
    } else {
	unit_literals.insert(lit);
	unit_trail.push_back(lit);
    }
}

void Clausal_reasoner::quantify(int var) {
    if (unit_literals.find(var) != unit_literals.end()) {
	err(false, "Attempt to quantify variable %d, but literal %d has already been assigned\n", var, var);
    } else if (unit_literals.find(-var) != unit_literals.end()) {
	err(false, "Attempt to quantify variable %d, but literal %d has already been assigned\n", var, -var);
    } else if (quantified_variables.find(var) != quantified_variables.end()) {
	err(false, "Attempt to quantify variable %d even already quantified\n", var);
    } else {
	quantified_variables.insert(var);
	uquant_trail.push_back(var);
    }
}

// Return TAUTOLOGY, CONFLICT, propagated unit, or zero
int Clausal_reasoner::propagate_clause(int cid) {
    int len = cnf->clause_length(cid);
    int result = CONFLICT;
    for (int lid = 0; lid < len; lid++) {
	int lit = cnf->get_literal(cid, lid);
	int var = IABS(lit);
	if (quantified_variables.find(var) != quantified_variables.end())
	    continue;
	else if (unit_literals.find(lit) != unit_literals.end()) {
	    result = TAUTOLOGY;
	    break;
	} else if (unit_literals.find(-lit) != unit_literals.end())
	    continue;
	else if (result == CONFLICT)
	    result = lit;
	else {
	    result = 0;
	    break;
	}
    }
    return result;
}


// Return true if unpropagated unit literal remains.
// Update next active clauses
bool Clausal_reasoner::unit_propagate() {
    next_active_clauses->clear();
    bool new_unit = false;
    for (int cid : *curr_active_clauses) {
	int rval = propagate_clause(cid);
	if (rval == CONFLICT) {
	    // Reduce to single conflict clause
	    for (int ccid : *next_active_clauses)
		deactivate_clause(ccid);
	    next_active_clauses->clear();
	    next_active_clauses->insert(cid);
	    new_unit = false;
	    bcp_units.clear();
	    break;
	} else if (rval == 0) {
	    next_active_clauses->insert(cid);
	    continue;
	} else if (rval == TAUTOLOGY) {
	    deactivate_clause(cid);
	    continue;
	} else {
	    // Derived unit literal
	    unit_literals.insert(rval);
	    bcp_units.push_back(rval);
	    deactivate_clause(cid);
	    new_unit = true;
	}
    }
    auto tmp = curr_active_clauses;
    curr_active_clauses = next_active_clauses;
    next_active_clauses = tmp;
    return new_unit;
}

bool Clausal_reasoner::bcp(int step_limit) {
    bcp_units.clear();
    for (int step = 1; step_limit == 0 || step < step_limit; step++) {
#if 0
	printf("BCP step %d.  Active clauses =", step);
	for (int cid : *curr_active_clauses)
	    printf(" %d", cid);
	printf(".  Unit literals =");
	for (int ulit : unit_literals)
	    printf(" %d", ulit);
	printf("\n");
#endif
	if (!unit_propagate())
	    break;
    }
    return has_conflict();
}

// Is there a conflict clause in the current state?
bool Clausal_reasoner::has_conflict() {
    if (curr_active_clauses->size() != 1)
	return false;
    for (int cid : *curr_active_clauses) {
	return propagate_clause(cid) == CONFLICT;
    }
    // Shouldn't get here
    return false;
}

cnf_archive_t Clausal_reasoner::extract() {
    std::vector<int> varx;
    start_build(varx, cnf->variable_count(), bcp_units.size() + curr_active_clauses->size());
    int ncid = 0;
    // Put in the derived unit literals
    for (int ulit : bcp_units) {
	new_clause(varx, ++ncid);
	add_literal(varx, ulit);
    }
    for (int ocid : *curr_active_clauses) {
	new_clause(varx, ++ncid);
	int len = cnf->clause_length(ocid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = cnf->get_literal(ocid, lid);
	    int var = IABS(lit);
	    if (unit_literals.find(-lit) == unit_literals.end() &&
		quantified_variables.find(var) == quantified_variables.end())
		add_literal(varx, lit);
	}
    }
    return finish_build(varx);
}

// Read NNF file and integrate into POG.  Return edge to new root
// Works with D4 version of NNF
int load_nnf(const char *nnfname) {
    return 0;
}

