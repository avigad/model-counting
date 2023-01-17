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
#include <map>
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

Clause::Clause(FILE *infile, bool &eof) {
    int rval;
    int lit;
    int c;
    is_tautology = false;
    contents = ilist_new(4);
    eof = true;

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
	eof = false;
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
    bool got_header = false;
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
		std::cerr << "Not valid CNF FILE.  Invalid header line" << std::endl;
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
	    got_header = true;
	    break;
	}
	if (c == EOF) {
	    read_failed = true;
	    std::cerr << "EOF encountered before reading any clauses" << std::endl;
	    return;
	}
    }
    if (!got_header) {
	std::cerr << "Not valid CNF FILE.  No header line found" << std::endl;
	read_failed = true;
	return;
    }
    while (1) {
	bool eof = false;
	Clause *clp = new Clause(infile, eof);
	if (eof || read_failed)
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
    int cid = clauses.size() + proof_clauses.size() + 1;
    proof_clauses.push_back(clp);
    if (clp->length() == 1) {
	int lit = (*clp)[0];
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
    }
    return cid;
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

void CNF::finish_command(bool add_zero) {
    if (add_zero)
	pwriter->finish_line("0");
    else
	pwriter->finish_line("");
}

int CNF::start_and(int var, ilist args) {
    pwriter->comment("AND operation");
    Clause *clp = new Clause();
    clp->add(var);
    for (int i = 0; i < ilist_length(args); i++) 
	clp->add(-args[i]);
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

void CNF::document_and(int cid, int var, ilist args) {
    if (verblevel < 2) 
	return;
    pwriter->comment("Implicit declarations");
    int len = ilist_length(args);
    ilist show = ilist_new(len+2);
    ilist_resize(show, len+2);
    show[0] = cid;
    show[1] = var;
    for (int i = 0; i < len; i++)
	show[i+2] = -args[i];
    pwriter->comment_list(show);
    show = ilist_resize(show, 3);
    for (int i = 0; i < ilist_length(args); i++) {
	show[0] = cid+i+1;
	show[1] = -var;
	show[2] = args[i];
	pwriter->comment_list(show);
    }
    ilist_free(show);
}


int CNF::start_or(int var, ilist args) {
    pwriter->comment("OR operation");
    int arg1 = args[0];
    int arg2 = args[1];
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

void CNF::document_or(int cid, int var, ilist args) {
    if (verblevel < 2)
	return
    pwriter->comment("Implicit declarations");
    int len = ilist_length(args);
    ilist show = ilist_new(len+2);
    ilist_resize(show, len+2);
    show[0] = cid;
    show[1] = -var;
    for (int i = 0; i < len; i++)
	show[i+2] = args[i];
    pwriter->comment_list(show);
    show = ilist_resize(show, 3);
    for (int i = 0; i < ilist_length(args); i++) {
	show[0] = cid+i+1;
	show[1] = var;
	show[2] = -args[i];
	pwriter->comment_list(show);
    }
    ilist_free(show);
}


// Got a new unit literal.
void CNF::new_unit(int lit, int cid, bool input) {
    if (input) {
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
	report(3, "Unit literal %d justified by input clause #%d\n", lit, cid);
	return;
    }
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
	push_derived_literal(lit, cid);
	report(3, "Unit literal %d already justified by clause #%d\n", lit, cid);
	return;
    }
    Clause *clp = new Clause();
    clp->add(lit);
    for (int alit : assigned_literals)
	clp->add(-alit);
    int ncid = start_assertion(clp);
    if (clp->length() > 1) {
	push_derived_literal(lit, ncid);
	push_clause(ncid);
    }
    // Print hints
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    add_hint(fid->second);
	}
    }
    add_hint(cid);
    finish_command(true);
    report(3, "Unit literal %d justified by proof clause #%d\n", lit, ncid);
}

void CNF::found_conflict(int cid) {
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
    if (clp->length() > 1)
	push_clause(ncid);
    add_hint(cid);
    finish_command(true);
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
	    continue;
	else if (cp->length() == 1) {
	    new_unit((*cp)[0], cid, true);
	    continue;
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
// Return false if formula falsified
// Each pass uses clauses from current active clauses and adds to next active clauses
// And then swaps the two sets
bool CNF::bcp() {
    bool converged = false;
    bool conflict = false;
    while (!converged && !conflict) {
	converged = true;
	if (verblevel >= 3) {
	    report(3, "BCP Pass.  Active clauses:");
	    for (int cid : *curr_active_clauses) {
		report(3, " %d", cid);
	    }
	    report(3, "\n");
	}
	for (int cid : *curr_active_clauses) {
	    if (conflict) {
		// Skip through clauses after conflict
		next_active_clauses->insert(cid);
		continue;
	    }
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
		    push_clause(cid);
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
		found_conflict(cid);
		push_clause(cid);
	    } else if (ulit != 0) {
		report(3, "    Unit %d\n", ulit);
		new_unit(ulit, cid, false);
		converged = false;
		push_clause(cid);
	    } else if (multi_active) {
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

// Generate set of hints for clause based on RUP validation
// Add clause as assertion
// Return false if fail
bool CNF::rup_validate(Clause *cltp) {
    // List of clause Ids that have been used in unit propagation
    std::vector<int> prop_clauses;
    // Initialize with all known units:
    for (int ulit : unit_literals) {
	auto fid = justifying_ids.find(ulit);
	if (fid != justifying_ids.end())
	    prop_clauses.push_back(fid->second);
    }
    if (verblevel >= 3) {
	report(3, "\nStarting RUP deriviation of clause ");
	cltp->show(stdout);
    }
    new_context();
    // Negate literals in target clause
    for (int idx = 0; idx < cltp->length(); idx++) {
	int tlit = (*cltp)[idx];
	if (unit_literals.find(-tlit) == unit_literals.end()) {
	    push_assigned_literal(-tlit);
	}
    }
    // Unit propagation
    bool converged = false;
    bool conflict = false;
    while (!converged && !conflict) {
	converged = true;
	if (verblevel >= 3) {
	    report(3, "BCP Pass.  Active clauses:");
	    for (int cid : *curr_active_clauses) {
		report(3, " %d", cid);
	    }
	    report(3, "\n");
	}
	for (int cid : *curr_active_clauses) {
	    if (conflict) {
		// After encountering conflict, skip over remaining clauses
		next_active_clauses->insert(cid);
		continue;
	    }
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
		    push_clause(cid);
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
		prop_clauses.push_back(cid);
		push_clause(cid);
	    } else if (ulit != 0) {
		report(3, "    Unit %d\n", ulit);
		prop_clauses.push_back(cid);
		push_derived_literal(ulit, cid);
		push_clause(cid);
		converged = false;
	    } else if (multi_active) {
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
    if (conflict) {
	// Construct hints in reverse order
	report(3, "Conflict found.  Constructing hints\n");
	std::vector<int> hints;
	std::unordered_set<int> used_set;
	std::reverse(prop_clauses.begin(), prop_clauses.end());
	used_set.insert(prop_clauses.front());
	for (int hid : prop_clauses) {
	    if (used_set.find(hid) != used_set.end()) {
		hints.push_back(hid);
		report(3, "  Clause #%d added to hints\n", hid);
		Clause *clp = (*this)[hid];
		for (int idx = 0; idx < clp->length(); idx++) {
		    int lit = (*clp)[idx];
		    auto fid = justifying_ids.find(-lit);
		    if (fid != justifying_ids.end()) {
			int jid = fid->second;
			used_set.insert(jid);
			report(3, "    Literal %d justified by clause #%d\n", -lit, jid);
		    } else {
			report(3, "    No justifying clause found for literal %d\n", -lit);
		    }
		}
	    } else
		report(3, "  Clause #%d not needed as hint\n", hid);
	}
	// Put hints in proper order
	std::reverse(hints.begin(), hints.end());
	int ncid = start_assertion(cltp);
	for (int hid : hints)
	    add_hint(hid);
	finish_command(true);
	curr_active_clauses->insert(ncid);
    }
    // Undo assignments
    pop_context();
    return conflict;
}


// Used to mark new layer in context stacks
#define CONTEXT_MARKER 0

void CNF::new_context() {
    context_literal_stack.push_back(CONTEXT_MARKER);
    context_clause_stack.push_back(CONTEXT_MARKER);
}

void CNF::push_assigned_literal(int lit) {
    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, already have -%d as unit\n", lit, lit);
    if (unit_literals.find(lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, it is already unit\n", lit);
    unit_literals.insert(lit);
    assigned_literals.push_back(lit);
    context_literal_stack.push_back(lit);
}

void CNF::push_derived_literal(int lit, int cid) {
    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, already have derived -%d as unit\n", lit, lit);
    if (unit_literals.find(lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, it is already unit\n", lit);
    unit_literals.insert(lit);
    justifying_ids[lit] = cid;
    context_literal_stack.push_back(lit);
}

void CNF::push_clause(int cid) {
    context_clause_stack.push_back(cid);
}

void CNF::pop_context() {
    while (true) {
	if (context_literal_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context literal stack\n");
	int lit = context_literal_stack.back(); context_literal_stack.pop_back();
	if (lit == CONTEXT_MARKER)
	    break;
	unit_literals.erase(lit);
	if (auto fid = justifying_ids.find(lit) == justifying_ids.end()) {
	    report(4, "  Restoring asserted literal %d\n", lit);
	    assigned_literals.pop_back();
	} else {
	    justifying_ids.erase(lit);
	    report(4, "  Restoring derived literal %d\n", lit);
	}
    }
    while (true) {
	if (context_clause_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context clause stack\n");
	int cid = context_clause_stack.back(); context_clause_stack.pop_back();
	if (cid == CONTEXT_MARKER)
	    break;
	curr_active_clauses->insert(cid);
	report(4, "  Reactivating clause %d\n", cid);
    }
}


// Partition set of active clauses into subsets, each using distinct sets of variables
// Each set denoted by reference variable
// var2rvar provides a mapping from each variable to the containing set's reference variable
// rvar2cset provides a mapping from the reference variable to the set of clauses
void CNF::partition_clauses(std::unordered_map<int,int> &var2rvar, std::unordered_map<int,std::vector<int>*> &rvar2clist) {
    // First figure out a partitioning of the variables
    // Map from variable to representative value in its partition
    // Mapping from representative var to set of variables
    var2rvar.clear();
    std::map<int,std::unordered_set<int>*> rvar2vset;
    for (int cid : *curr_active_clauses) {
	Clause *cp = (*this)[cid];
	if (cp->length() < 2)
	    continue;
	for (int i = 0; i < cp->length(); i++) {
	    int lit = (*cp)[i];
	    int var = IABS(lit);
	    if (unit_literals.find(-lit) != unit_literals.end())  {
		// Literal currently falsified
		continue;
	    }
	    if (unit_literals.find(lit) != unit_literals.end())  {
		// Clause satisfied.  This is not expected
		err(true, "Satisfied clause #%d (unit literal %d) found during clause partitionning\n",
		    cid, lit);
		return;
	    }
	    if (var2rvar.find(var) == var2rvar.end()) {
		var2rvar[var] = var;
		std::unordered_set<int> *nset = new std::unordered_set<int>;
		rvar2vset[var] = nset;
		nset->insert(var);
	    }
	}
    }
    for (int cid : *curr_active_clauses) {
	Clause *cp = (*this)[cid];
	for (int i = 0; i < cp->length(); i++) {
	    int lit1 = (*cp)[i];
	    int var1 = IABS(lit1);
	    auto fid1 = var2rvar.find(var1);
	    if (fid1 == var2rvar.end())
		continue;
	    int rvar1 = fid1->second;
	    std::unordered_set<int>*set1 = rvar2vset.find(rvar1)->second;
	    for (int j = i+1; j < cp->length(); j++) {
		int lit2 = (*cp)[j];
		int var2 = IABS(lit2);
		auto fid2 = var2rvar.find(var2);
		if (fid2 == var2rvar.end())
		    continue;
		int rvar2 = fid2->second;
		if (rvar1 != rvar2) {
		    std::unordered_set<int>*set2 = rvar2vset.find(rvar2)->second;
		    // Merge smaller into larger
		    if (set1->size() < set2->size()) {
			std::unordered_set<int>*tset = set1;
			set1 = set2;
			set2 = tset;
			int trvar = rvar1;
			rvar1 = rvar2;
			rvar2 = trvar;
		    }
		    for (int mvar : *set2) {
			set1->insert(mvar);
			var2rvar[mvar] = rvar1;
		    }
		    rvar2vset.erase(rvar2);
		    delete set2;
		}
	    }
	}
    }
    report(3, "Identified %d partitions\n", rvar2vset.size());
    rvar2clist.clear();
    for (auto fid : rvar2vset) {
	int rvar = fid.first;
	// Don't need variable set anymore
	delete fid.second;
	std::vector<int> *clist = new std::vector<int>;
	rvar2clist[rvar] = clist;
    }
    // Assign clauses to sets
    for (int cid : *curr_active_clauses) {
	Clause *cp = (*this)[cid];
	for (int i = 0; i < cp->length(); i++) {
	    int lit = (*cp)[i];
	    int var = IABS(lit);
	    auto fid = var2rvar.find(var);
	    if (fid == var2rvar.end())
		continue;
	    int rvar = fid->second;
	    std::vector<int> *clist = rvar2clist.find(rvar)->second;
	    clist->push_back(cid);
	}
    }
}
