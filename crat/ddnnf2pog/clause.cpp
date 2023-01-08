/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
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


#include <iostream>
#include <ctype.h>
#include <algorithm>
#include <cstring>
#include "clause.hh"
#include "report.h"

static int skip_line(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return c;
    }
    return c;
}

// Put literals in descending order of the variables
static bool abs_less(int x, int y) {
    return abs(x) > abs(y);
}


Clause::Clause() { contents = ilist_new(0); is_tautology = false; }

Clause::~Clause() { ilist_free(contents); }

Clause::Clause(int *array, size_t len) {
    is_tautology = false;
    contents = ilist_new(len);
    for (int i = 0; i < len; i++)
	add(array[i]);
    canonize();
}

Clause::Clause(FILE *infile) {
    int rval;
    int lit;
    int c;
    is_tautology = false;
    contents = ilist_new(4);

    // Skip blank lines and comments
    while ((c = getc(infile)) != EOF) {
	if (c == 'c')
	    c = skip_line(infile);
	if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    break;
	}
    }

    while ((rval = fscanf(infile, "%d", &lit)) == 1) {
	if (lit == 0)
	    break;
	else
	    add(lit);
    }
    canonize();
}

void Clause::add(int val) {
    contents = ilist_push(contents, val);
}

size_t Clause::length() {
    if (is_tautology)
	return 0;
    return ilist_length(contents);
}

bool Clause::tautology() {
    return is_tautology;
}

int Clause::max_variable() {
    int mvar = 0;
    if (is_tautology)
	return 0;
    for (int i = 0; i < length(); i++) {
	int var = abs(contents[i]);
	mvar = std::max(var, mvar);
    }
    return mvar;
}

int * Clause::data() {
    return contents;
}

int& Clause::operator[](int i) {
    return contents[i];
}

bool Clause::satisfied(char *assignment) {
    bool found = is_tautology;
    for (int i = 0; !found && i < ilist_length(contents); i++) {
	int lit = contents[i];
	found = (lit < 0 && assignment[-lit-1] == 0) || (lit > 0 && assignment[lit-1] == 1);
    }
    return found;
}

void Clause::canonize() {
    std::sort(contents, contents + length(), abs_less);
    int last_lit = 0;
    size_t read_pos = 0;
    size_t write_pos = 0;
    while(read_pos < length()) {
	int lit = contents[read_pos++];
	if (abs(lit) == abs(last_lit)) {
	    if (lit != last_lit) {
		// Opposite literals encountered
		is_tautology = true;
		break;
	    }
	} else {
	    contents[write_pos++] = lit;
	}
	last_lit = lit;
    }
    if (is_tautology) {
	contents = ilist_resize(contents, 2);
	contents[0] = abs(last_lit);
	contents[1] = -abs(last_lit);
    } else
	contents = ilist_resize(contents, write_pos);
}

void Clause::show() {
    if (is_tautology) {
	std::cout << "c Tautology" << std::endl;
	std::cout << "1 -1 0" << std::endl;
	return;
    }
    for (int i = 0; i < length(); i++)
	std::cout << contents[i] << ' ';
    std::cout << '0' << std::endl;
}

void Clause::show(std::ofstream &outstream) {
    if (is_tautology) {
	outstream << "c Tautology" << std::endl;
	outstream << "1 -1 0" << std::endl;
	return;
    }
    for (int i = 0; i < length(); i++)
	outstream << contents[i] << ' ';
    outstream << '0' << std::endl;
}

void Clause::show(FILE *outfile) {
    if (is_tautology) {
	fprintf(outfile, "c Tautology\n");
	fprintf(outfile, "1 -1 0\n");
	return;
    }
    for (int i = 0; i < length(); i++)
	fprintf(outfile, "%d ", contents[i]);
    fprintf(outfile, "0\n");
}

void Clause::write(Writer *writer) {
    if (is_tautology) {
	int tclause[2 + ILIST_OVHD];
	ilist ils = ilist_make(tclause, 2);
	ilist_fill2(ils, 1, -1);
	writer->write_list(ils);
	return;
    }
    writer->write_list(contents);
}

CNF::CNF() { read_failed = false; max_input_var = 0; pwriter = NULL; }

CNF::CNF(FILE *infile) { 
    int expectedMax = 0;
    int expectedCount = 0;
    read_failed = false;
    max_input_var = 0;
    pwriter = NULL;
    int c;
    // Look for CNF header
    while ((c = getc(infile)) != EOF) {
	if (isspace(c)) 
	    continue;
	if (c == 'c')
	    c = skip_line(infile);
	if (c == EOF) {
	    std::cerr << "Not valid CNF File.  No header line found" << std::endl;
	    read_failed = true;
	    return;
	}
	if (c == 'p') {
	    char field[20];
	    if (fscanf(infile, "%s", field) != 1) {
		std::cerr << "Not valid CNF FILE.  No header line found" << std::endl;
		read_failed = true;
		return;
	    }
	    if (strcmp(field, "cnf") != 0) {
		std::cerr << "Not valid CNF file.  Header shows type is '" << field << "'" << std::endl;
		read_failed = true;
		return;
	    }
	    if (fscanf(infile, "%d %d", &expectedMax, &expectedCount) != 2) {
		std::cerr << "Invalid CNF header" << std::endl;
		read_failed = true;
		return;
	    } 
	    c = skip_line(infile);
	    break;
	}
	if (c == EOF) {
	    read_failed = true;
	    std::cerr << "EOF encountered before reading any clauses" << std::endl;
	    return;
	}
    }
    while (1) {
	Clause *clp = new Clause(infile);
	if (clp->length() == 0)
	    break;
	add(clp);
	int mvar = clp->max_variable();
	max_input_var = std::max(max_input_var, mvar);
    }
    if (max_input_var > expectedMax) {
	std::cerr << "Encountered variable " << max_input_var << ".  Expected max = " << expectedMax << std::endl;
	read_failed = true;
	return;
    }
    if (clause_count() != expectedCount) {
	std::cerr << "Read " << clause_count() << " clauses.  Expected " << expectedCount << std::endl;
	read_failed = true;
	return;
    }
}

bool CNF::failed() {
    return read_failed;
}

void CNF::add(Clause *clp) {
    clauses.push_back(clp);
}

Clause * CNF::operator[](int cid) {
    int input_count = clauses.size();
    int proof_count = proof_clauses.size();
    if (cid <= input_count)
	return clauses[cid-1];
    else if (cid <= input_count + proof_count)
	return proof_clauses[cid - input_count - 1];
    else {
	err(true, "Fatal.  Trying to acess clause #%d.  Have %d input and %d proof clauses\n", cid, input_count, proof_count);
	exit(1);
    }
}


void CNF::show() {
    std::cout << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show();
    }
}

void CNF::show(std::ofstream &outstream) {
    outstream << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show(outstream);
    }
}

void CNF::show(FILE *outfile) {
    fprintf(outfile, "p cnf %d %d\n", max_input_var, (int) clause_count());
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show(outfile);
    }
}

size_t CNF::clause_count() {
    return clauses.size();
}

int CNF::max_variable() {
    return max_input_var;
}

int CNF::satisfied(char *assignment) {
    for (int cid = 1; cid <= clauses.size(); cid++) {
	Clause *cp = clauses[cid-1];
	if (!cp->satisfied(assignment))
	    return cid;
    }
    return 0;
}

// Proof related
int CNF::add_proof_clause(Clause *clp) {
    proof_clauses.push_back(clp);
    return clauses.size() + proof_clauses.size();
}

int CNF::start_assertion(Clause *clp) {
    int cid = add_proof_clause(clp);
    pwriter->start_assertion(cid);
    clp->write(pwriter);
    return cid;
}

void CNF::add_hint(int hid) {
    pwriter->add_int(hid);
}

void CNF::finish_assertion() {
    pwriter->finish_line("0");
}

int CNF::start_and(int var, ilist args) {
    Clause *clp = new Clause();
    clp->add(var);
    for (int i = 0; i < ilist_length(args); i++) {
	clp->add(-args[i]);
    }
    int cid = add_proof_clause(clp);
    for (int i = 0; i < ilist_length(args); i++) {
	Clause *aclp = new Clause();
	aclp->add(-var);
	aclp->add(args[i]);
	add_proof_clause(aclp);
    }
    pwriter->start_and(cid, var);
    pwriter->write_list(args);
    return cid;
}

int CNF::start_or(int var, int arg1, int arg2) {
    Clause *clp = new Clause();
    clp->add(-var); clp->add(arg1); clp->add(arg2);
    int cid = add_proof_clause(clp);
    Clause *aclp1 = new Clause();
    aclp1->add(var); aclp1->add(-arg2);
    add_proof_clause(aclp1);
    Clause *aclp2 = new Clause();
    aclp2->add(var); aclp2->add(-arg2);
    add_proof_clause(aclp2);
    pwriter->start_or(cid, var);
    pwriter->add_int(arg1); pwriter->add_int(arg2);
    return cid;
}

// Got a new unit literal.
int CNF::new_unit(int lit, int cid, bool input) {
    unit_literals.insert(lit);
    if (input) {
	justifying_ids[lit] = cid;
	report(3, "Unit literal %d justified by input clause #%d\n", lit, cid);
	return cid;
    }
    derived_literals.push_back(lit);
    Clause *cp = (*this)[cid];
    int clen = cp->length();
    // Optimization: Don't generate new clause if unit implied by context literals
    bool need_new = false;
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	if (justifying_ids.find(-clit) != justifying_ids.end())
	    need_new = true;
    }
    if (!need_new) {
	justifying_ids[lit] = cid;
	report(3, "Unit literal %d already justified by clause #%d\n", lit, cid);
	return cid;
    }
    Clause *clp = new Clause();
    clp->add(lit);
    for (int alit : assigned_literals)
	clp->add(-alit);
    int ncid = start_assertion(clp);
    justifying_ids[lit] = ncid;
    report(3, "Unit literal %d justified by proof clause #%d\n", lit, ncid);
    // Print hints
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    add_hint(fid->second);
	}
    }
    add_hint(cid);
    finish_assertion();
    return ncid;
}

int CNF::found_conflict(int cid) {
    Clause *clp = new Clause();
    for (int alit : assigned_literals)
	clp->add(-alit);
    int ncid = start_assertion(clp);
    // Print hints
    Clause *cp = (*this)[cid];
    int clen = cp->length();
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    add_hint(fid->second);
	}
    }
    add_hint(cid);
    finish_assertion();
    if (clp->length() == 1) {
	int lit = (*clp)[0];
	unit_literals.insert(lit);
	justifying_ids[lit] = ncid;
	report(3, "Unit literal %d justified by conflict proof clause #%d\n", lit, ncid);
    }
    return ncid;
}

// Enable POG generation
bool CNF::enable_pog(PogWriter *pw) {
    pwriter = pw;

    // Set up active clauses
    curr_active_clauses = new std::set<int>;
    next_active_clauses = new std::set<int>;

    // Scan all clauses.  Find unit clauses.  Register non-tautologies
    int cid = 0;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	cid++;
	Clause *cp = *clp;
	if (cp->tautology())
	    satisfied_ids.push_back(cid);
	else if (cp->length() == 1) {
	    new_unit((*cp)[0], cid, true);
	    satisfied_ids.push_back(cid);
	}
	else
	    curr_active_clauses->insert(cid);
    }
    if (!bcp()) {
	pwriter->comment("Read failed.  Formula unsatisfiable");
	return false;
    };
    return true;
}

// Perform Boolean constraint propagation
// Return False if formula falsified
// Each pass uses clauses from current active clauses and adds to next active clauses
// And then swaps the two sets
bool CNF::bcp() {
    bool done = false;
    bool conflict = false;
    while (!done) {
	done = true;
	if (verblevel >= 3) {
	    report(3, "BCP Pass.  Active clauses:");
	    for (int cid : *curr_active_clauses) {
		report(3, " %d", cid);
	    }
	    report(3, "\n");
	}
	for (int cid : *curr_active_clauses) {
	    int ulit = 0;
	    bool multi_active = false;
	    conflict = true;
	    Clause *cp  = (*this)[cid];
	    if (verblevel >= 3) {
		report(3, "  Checking clause #%d: ", cid);
		cp->show(stdout);
		report(3, "  Unit literals:");
		for (int ulit : unit_literals) {
		    report(3, " %d", ulit);
		}
		report(3, "\n");
	    }
	    for (int idx = 0; idx < cp->length(); idx++) {
		int clit = (*cp)[idx];
		if (unit_literals.find(clit) != unit_literals.end()) {
		    report(3, "    Clause satisfied by unit %d\n", clit);
		    // Clause satisifed.
		    ulit = 0;
		    conflict = false;
		    multi_active = false;
		    satisfied_ids.push_back(cid);
		    break;
		} else if (unit_literals.find(-clit) != unit_literals.end()) {
		    report(3, "    Literal %d falsified\n", clit);
		    continue;
		} else if (ulit == 0) {
		    report(3, "    Potential unit %d\n", clit);
		    // Potential unit
		    ulit = clit;
		    conflict = false;
		} else {
		    report(3, "    Additional unassigned literal %d\n", clit);
		    // Multiple unassigned literals
		    ulit = 0;
		    multi_active = true;
		    break;
		}
	    }
	    if (conflict) {
		report(3, "    Conflict\n");
		int ncid = found_conflict(cid);
		satisfied_ids.push_back(cid);
		next_active_clauses->insert(ncid);
		done = true;
		break;
	    }
	    if (ulit != 0) {
		report(3, "    Unit %d\n", ulit);
		int ncid = new_unit(ulit, cid, false);
		next_active_clauses->insert(ncid);
		satisfied_ids.push_back(cid);
		done = false;
	    } 
	    if (multi_active) {
		report(3, "    Still active\n");
		next_active_clauses->insert(cid);
	    }
	}
	// Swap active clause sets
	std::set<int> *tmp =  curr_active_clauses;
	curr_active_clauses = next_active_clauses;
	next_active_clauses = tmp;
	next_active_clauses->clear();
    }
    return !conflict;
}

bool CNF::new_context(int lit) {
    if (unit_literals.find(-lit) != unit_literals.end())
	return false;
    assigned_literals.push_back(lit);
    literal_start_index.push_back(derived_literals.size());
    unit_literals.insert(lit);
    satisfied_start_index.push_back(satisfied_ids.size());
    return bcp();
}

bool CNF::pop_context(int levels) {
    for (int lcount = 0; lcount < levels; lcount++) {
	if (assigned_literals.size() == 0)
	    err(true, "Attempt to pop below initial level\n");
	int alit = assigned_literals.back(); assigned_literals.pop_back();
	unit_literals.erase(alit);

	int spos = literal_start_index.back(); literal_start_index.pop_back();
	for (int pos = spos; pos < derived_literals.size(); pos++)
	    unit_literals.erase(derived_literals[pos]);
	derived_literals.resize(spos);

	int tpos = satisfied_start_index.back(); satisfied_start_index.pop_back();
	for (int pos = tpos; pos < satisfied_ids.size(); pos++) {
	    int cid = satisfied_ids[pos];
	    report(3, "Restoring clause #%d to active status\n", cid);
	    curr_active_clauses->insert(cid);
	}
	satisfied_ids.resize(tpos);
    }
    return bcp();
}
