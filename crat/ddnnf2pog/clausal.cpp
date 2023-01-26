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
#include "clausal.hh"
#include "report.h"

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

// Put literals in ascending order of the variables
static bool abs_less(int x, int y) {
    return abs(x) < abs(y);
}

Clause::Clause() { contents = ilist_new(0); is_tautology = false; }

Clause::~Clause() { 
    ilist_free(contents);
}

Clause::Clause(int *array, size_t len) {
    is_tautology = false;
    contents = ilist_new(len);
    for (int i = 0; i < len; i++)
	add(array[i]);
    canonize();
}

Clause::Clause(Clause *np) {
    is_tautology = false;
    int len = np->length();
    contents = ilist_new(len);
    for (int i = 0; i < len; i++)
	add((*np)[i]);
}

Clause::Clause(FILE *infile, bool from_proof, bool *eof) {
    int rval;
    int lit;
    int c;
    is_tautology = false;
    contents = ilist_new(4);
    *eof = true;

    // Skip blank lines and comments
    while ((c = getc(infile)) != EOF) {
	if (c == 'c')
	    c = skip_line(infile);
	else if (from_proof && c == 'd')
	    c = skip_line(infile);
	else if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    break;
	}
    }

    while ((rval = fscanf(infile, "%d", &lit)) == 1) {
	*eof = false;
	if (lit == 0)
	    break;
	else
	    add(lit);
    }
    if (!from_proof)
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

bool Clause::contains(int lit) {
    for (int i = 0; i < ilist_length(contents); i++)
	if (contents[i] == lit)
	    return true;
    return false;
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

Cnf::Cnf() { read_failed = false; max_input_var = 0; }

Cnf::Cnf(FILE *infile) { 
    int expectedMax = 0;
    int expectedCount = 0;
    read_failed = false;
    max_input_var = 0;
    bool got_header = false;
    bool no_header = false;
    int c;
    // Look for CNF header
    while ((c = getc(infile)) != EOF) {
	if (isspace(c)) 
	    continue;
	if (c == 'c' || c == 'd' || c == 'v' || c == 's')
	    c = skip_line(infile);
	if (c == EOF) {
	    err(false, "Not valid CNF file.  No header line found\n");
	    read_failed = true;
	    return;
	}
	if (c == 'p') {
	    char field[20];
	    if (fscanf(infile, "%s", field) != 1) {
		err(false, "Not valid CNF file.  Invalid header line\n");
		read_failed = true;
		return;
	    }
	    if (strcmp(field, "cnf") != 0) {
		err(false, "Not valid CNF file.  Header line shows type is '%s'\n", field);
		read_failed = true;
		return;
	    }
	    if (fscanf(infile, "%d %d", &expectedMax, &expectedCount) != 2) {
		err(false, "Invalid CNF header\n");
		read_failed = true;
		return;
	    } 
	    c = skip_line(infile);
	    got_header = true;
	    break;
	}
	if (c == EOF) {
	    err(false, "Invalid CNF.  EOF encountered before reading any clauses\n");
	    read_failed = true;
	    return;
	}
	if (isdigit(c) || c == '-') {
	    no_header = true;
	    ungetc(c, infile);
	    break;
	}
    }
    if (!got_header && !no_header) {
	err(false, "Not valid CNF.  No header line found\n");
	read_failed = true;
	return;
    }
    while (1) {
	bool eof = false;
	Clause *clp = new Clause(infile, !got_header, &eof);
	if (eof || read_failed)
	    break;
	add(clp);
	int mvar = clp->max_variable();
	max_input_var = std::max(max_input_var, mvar);
    }
    if (!no_header && max_input_var > expectedMax) {
	err(false, "Invalid CNF.  Encountered variable %d. Expected max = %d\n",  max_input_var, expectedMax);
	read_failed = true;
	return;
    }
    if (!no_header && clause_count() != expectedCount) {
	err(false, "Read %d clauses.  Expected %d\n", clause_count(), expectedCount);
	read_failed = true;
	return;
    }
}

// Delete the clauses
Cnf::~Cnf() { 
#if 0
    for (Clause *np : clauses) {
	delete np;
    }
#endif
}

bool Cnf::failed() {
    return read_failed;
}

void Cnf::add(Clause *clp) {
    int mvar = clp->max_variable();
    max_input_var = std::max(max_input_var, mvar);
    clauses.push_back(clp);
}

Clause * Cnf::get_input_clause(int cid) {
    int input_count = clauses.size();
    if (cid <= input_count)
	return clauses[cid-1];
    else {
	err(true, "Fatal.  Trying to access clause #%d.  Have %d input clauses\n", cid, input_count);
	exit(1);
    }
}

Clause * Cnf::operator[](int cid) {
    return get_input_clause(cid);
}

void Cnf::show() {
    std::cout << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show();
    }
}

void Cnf::show(std::ofstream &outstream) {
    outstream << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show(outstream);
    }
}

void Cnf::show(FILE *outfile) {
    fprintf(outfile, "p cnf %d %d\n", max_input_var, (int) clause_count());
    for (std::vector<Clause *>::iterator clp = clauses.begin(); clp != clauses.end(); clp++) {
	(*clp)->show(outfile);
    }
}

size_t Cnf::clause_count() {
    return clauses.size();
}

int Cnf::max_variable() {
    return max_input_var;
}

int Cnf::satisfied(char *assignment) {
    for (int cid = 1; cid <= clauses.size(); cid++) {
	Clause *cp = clauses[cid-1];
	if (!cp->satisfied(assignment))
	    return cid;
    }
    return 0;
}

// Support for generating reduced CNF, running through SAT solver, and mapping proof steps back to original
Cnf_reduced::Cnf_reduced() : Cnf() {
    emitted_proof_clauses = 0;
    unsatisfiable = false;
    delete_files = true;
}

Cnf_reduced::~Cnf_reduced() {
    for (Clause *np : proof_clauses) {
	if (np)
	    delete np;
    }
    // Could delete the temporary files here.
    for (const char *fname : file_names) {
	if (delete_files)
	    remove(fname);
	free((void *) fname);
    }
}

const char *Cnf_reduced::get_file_name() {
    if (file_names.size() >= 1)
	return file_names[0];
    else
	return "Unknown";
}

void Cnf_reduced::add_clause(Clause *np, std::unordered_set<int> &unit_literals, int cid) {
    std::vector<int> lits;
    bool satisfied = false;
    for (int i = 0; i < np->length(); i++) {
	int lit = (*np)[i];
	if (unit_literals.find(lit) != unit_literals.end()) {
	    satisfied = true;
	    break;
	} else if (unit_literals.find(-lit) == unit_literals.end())
	    lits.push_back(lit);
    }
    if (!satisfied) {
	add(new Clause(lits.data(), lits.size()));
	inverse_cid[clause_count()] = cid;
	if (lits.size() == 0)
	    unsatisfiable = true;
    }
}

bool Cnf_reduced::run_solver() {
    static int vnum = 1000000;
    char tname[100];
    char cmd[150];
    
    if (unsatisfiable) {
	err(false, "Reduced CNF contains empty clause\n");
	return true;
    }

    snprintf(tname, 100, "reduction-%d.cnf", ++vnum);
    
    FILE *cout = fopen(tname, "w");
    if (cout == NULL) {
	err(false, "Couldn't open temporary CNF file %s\n", tname);
	return false;
    }
    const char *fname = archive_string(tname);
    file_names.push_back(fname);
    show(cout);
    fclose(cout);
    report(3, "Wrote file with %d clauses to %s\n", clause_count(), fname);
    
    snprintf(cmd, 150, "cadical --unsat -q --no-binary %s -", fname);
    FILE *sfile = popen(cmd, "r");
    if (sfile == NULL) {
	err(true, "Couldn't execute command '%s'\n", cmd);
    }
    Cnf pclauses(sfile);
    pclose(sfile);

    report(3, "Read %d proof clauses\n", pclauses.clause_count());
    if (verblevel >= 5)
	pclauses.show();

    if (pclauses.clause_count() == 0) {
	err(false, "Execution of command '%s' yielded no proof clauses\n", cmd);
	return false;
    }

    Clause *lnp = pclauses[pclauses.clause_count()];
    if (lnp == NULL) {
	err(false, "Invalid final clause after executing command '%s'\n", cmd);
	return false;
    }
    if (lnp->length() != 0) {
	err(false, "Execution of command '%s' did not generate empty clause\n", cmd);	
	return false;
    }

    for (int cid = 1; cid <= pclauses.clause_count(); cid++) {
	Clause *pnp = pclauses[cid];
	proof_clauses.push_back(pnp);
	if (pnp->length() == 0)
	    break;
    }
    report(3, "File %s.  %d input clauses --> %d proof clauses\n", fname, clause_count(), proof_clauses.size());

    return true;
}

bool Cnf_reduced::run_hinting_solver() {
    static int vnum = 1000000;
    char tcnfname[100];
    char tlratname[100];
    char cmd[350];

    if (unsatisfiable) {
	err(false, "Reduced CNF contains empty clause\n");
	return true;
    }

    snprintf(tcnfname, 100, "reduction-%d.cnf", ++vnum);
    FILE *cout = fopen(tcnfname, "w");
    if (cout == NULL) {
	err(false, "Couldn't open temporary CNF file %s\n", tcnfname);
	return false;
    }
    const char *cnfname = archive_string(tcnfname);
    file_names.push_back(cnfname);
    show(cout);
    fclose(cout);
    report(3, "Wrote file with %d clauses to %s\n", clause_count(), cnfname);
    
    snprintf(tlratname, 100, "reduction-%d.lrat", vnum);
    const char *lratname = archive_string(tlratname);
    file_names.push_back(lratname);

    snprintf(cmd, 350, "cadical --no-binary --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnfname, cnfname, lratname);
    int rc = system(cmd);
    if (rc != 0)
	err(false, "Executing command '%s' yielded return code %d\n", cmd, rc);
    FILE *lfile = fopen(lratname, "r");
    if (!lfile) {
	err(false, "Couldn't open generated LRAT file\n", lratname);
	return false;
    }
    if (!load_hinted_proof(lfile)) {
	err(false, "Failed to read generated LRAT file\n", lratname);
	return false;
    }
    if (proof_clauses.size() == 0) {
	err(false, "Execution of command '%s' yielded no proof clauses\n", cmd);
	return false;
    }

    Clause *lnp = proof_clauses.back();
    if (lnp->length() != 0) {
	err(false, "Execution of command '%s' did not generate empty clause\n", cmd);	
	return false;
    }
    report(3, "File %s.  %d input clauses --> %d proof clauses\n", cnfname, clause_count(), proof_clauses.size());
    return true;
}


// Read proof clauses + hints in LRAT format.
// Ignore deletions
// Return true if successful
bool Cnf_reduced::load_hinted_proof(FILE *infile) {
    int nclause = clause_count();
    std::unordered_map<int,int> lrat2local;
    int next_id = nclause + 1;
    while (find_token(infile)) {
	int sid = 0;
	if (fscanf(infile, "%d", &sid) != 1) {
	    err(false, "Couldn't read step Id in LRAT file.  Should be at step #%d\n", next_id);
	    return false;
	}
	if (!find_token(infile)) {
	    err(false, "EOF found while trying to parse proof step #%d\n", next_id);
	}
	int c = getc(infile);
	if (c == EOF) {
	    err(false, "EOF found while trying to parse proof step #%d\n", sid);
	    return false;
	}
	if (c == 'd') {
	    c = skip_line(infile);
	    if (c == EOF) {
		err(false, "EOF found while trying to parse proof step #%d\n", sid);
		return false;
	    }
	    ungetc(c, infile);
	    continue;
	} else
	    ungetc(c, infile);
	// Here's the good stuff
	bool eof;
	Clause *np = new Clause(infile, true, &eof);
	if (np == NULL || eof) {
	    err(false, "Error encountered while trying to read literals from proof step #%d\n", sid);
	    return false;
	}
	Clause *hp = new Clause(infile, true, &eof);
	if (hp == NULL || eof) {
	    err(false, "Error encountered while trying to read hints from proof step #%d\n", sid);
	    return false;
	}
	lrat2local[sid] = next_id;
	// Fix up hints
	for (int i = 0; i < hp->length(); i++) {
	    int hint = (*hp)[i];
	    int nhint = (hint <= nclause) ? hint : lrat2local.find(hint)->second;
	    (*hp)[i] = nhint;
	}
	proof_clauses.push_back(np);
	proof_hints.push_back(hp);
	next_id++;
    }
    return true;
}

// Retrieve hints for next clause in proof.
// Remap hint clause Ids to ones that match those in the larger proof
// start_id should be Id for first clause in proof sequence
Clause * Cnf_reduced::get_proof_hint(int start_id) {
    if (emitted_proof_clauses >= proof_hints.size())
	return NULL;
    Clause *hp = proof_hints[emitted_proof_clauses];
    Clause *nhp = new Clause();
    int ccount = clause_count();
    for (int i = 0; i < hp->length(); i++) {
	int hint = (*hp)[i];
	int nhint = hint <= ccount ? inverse_cid[hint] : start_id + hint - ccount - 1;
	nhp->add(nhint);
    }
    delete hp;
    return nhp;
}

// Retrieve next clause in proof.  Convert it to one usable by parent solver
Clause * Cnf_reduced::get_proof_clause(std::vector<int> *context) {
    if (emitted_proof_clauses >= proof_clauses.size())
	return NULL;
    Clause *np = proof_clauses[emitted_proof_clauses];
    Clause *nnp = new Clause(np);
    for (int lit : *context) 
	nnp->add(-lit);
    delete np;
    proof_clauses[emitted_proof_clauses++] = NULL;
    return nnp;
}

// Proof related
Cnf_reasoner::Cnf_reasoner(FILE *infile) : Cnf(infile) { 
    pwriter = NULL;
    asserting = false;
    unsatisfiable = false;
    use_drat = true;
    multi_literal = true;
    use_lemmas = true;
    delete_files = true;
}

Clause * Cnf_reasoner::get_clause(int cid) {
    int input_count = clause_count();
    int proof_count = proof_clauses.size();
    if (cid <= input_count)
	return get_input_clause(cid);
    else if (cid <= input_count + proof_count)
	return proof_clauses[cid - input_count - 1];
    else {
	err(true, "Fatal.  Trying to acess clause #%d.  Have %d input and %d proof clauses\n", cid, input_count, proof_count);
	exit(1);
    }
}


Clause * Cnf_reasoner::operator[](int cid) {
    return get_clause(cid);
}

bool Cnf_reasoner::is_unsatisfiable() {
    return unsatisfiable;
}

int Cnf_reasoner::add_proof_clause(Clause *clp) {
    int cid = clause_count() + proof_clauses.size() + 1;
    proof_clauses.push_back(clp);
    if (clp->length() == 0)
	unsatisfiable = true;
    else if (clp->length() == 1) {
	int lit = (*clp)[0];
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
    }
    return cid;
}

int Cnf_reasoner::start_assertion(Clause *clp) {
    int cid = add_proof_clause(clp);
    pwriter->start_assertion(cid);
    clp->write(pwriter);
    std::vector<int> *dvp = new std::vector<int>();
    dvp->push_back(cid);
    asserting = true;   
    deletion_stack.push_back(dvp);
    return cid;
}

void Cnf_reasoner::add_hint(int hid) {
    pwriter->add_int(hid);
    if (asserting) {
	std::vector<int> *dvp = deletion_stack.back();
	dvp->push_back(hid);
    }
}

void Cnf_reasoner::add_hints(Clause *hp) {
    for (int i = 0; i < hp->length(); i++) 
	add_hint((*hp)[i]);
}


void Cnf_reasoner::finish_command(bool add_zero) {
    if (add_zero)
	pwriter->finish_line("0");
    else
	pwriter->finish_line("");
    asserting = false;
}

void Cnf_reasoner::document_input(int cid) {
    ilist show = ilist_new(0);
    Clause *cp = get_clause(cid);
    show = ilist_push(show, cid);
    for (int i = 0; i < cp->length(); i++)
	show = ilist_push(show, (*cp)[i]);
    show = ilist_push(show, 0);
    pwriter->comment_list(show);
    ilist_free(show);
}

int Cnf_reasoner::start_and(int var, ilist args) {
    pwriter->comment("Operation N%d_AND", var);
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

void Cnf_reasoner::document_and(int cid, int var, ilist args) {
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


int Cnf_reasoner::start_or(int var, ilist args) {
    pwriter->comment("Operation N%d_OR", var);
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

void Cnf_reasoner::document_or(int cid, int var, ilist args) {
    if (verblevel < 2)
	return;
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
void Cnf_reasoner::new_unit(int lit, int cid, bool input) {
    if (input) {
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
	report(3, "Unit literal %d justified by input clause #%d\n", lit, cid);
	return;
    }
    Clause *cp = get_clause(cid);
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

int Cnf_reasoner::quick_validate_literal(int lit, int cid1, int cid2) {
    Clause *clp = new Clause();
    clp->add(lit);
    for (int alit : assigned_literals)
	clp->add(-alit);
    int ncid = start_assertion(clp);
    if (clp->length() > 1) {
	push_derived_literal(lit, ncid);
	push_clause(ncid);
    }
    add_hint(cid1);
    add_hint(cid2);
    finish_command(true);
    return ncid;
}

int Cnf_reasoner::found_conflict(int cid) {
    Clause *clp = NULL;
    int ncid = 0;
    // Print hints
    Clause *cp = get_clause(cid);
    int clen = cp->length();
    bool found_hint = false;
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    if (!found_hint) {
		found_hint = true;
		clp = new Clause();
		for (int alit : assigned_literals)
		    clp->add(-alit);
		ncid = start_assertion(clp);

	    }
	    add_hint(fid->second);
	}
    }
    if (!found_hint)
	return cid;
    if (clp->length() > 1)
	push_clause(ncid);
    add_hint(cid);
    finish_command(true);
    return ncid;
}

// Enable POG generation
bool Cnf_reasoner::enable_pog(Pog_writer *pw) {
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
    int ncid = bcp();
    if (ncid > 0) {
	pwriter->comment("Read failed.  Formula unsatisfiable (justifying ID = %d)", ncid);
	return false;
    };
    return true;
}

// Perform Boolean constraint propagation
// Return ID of any generated conflict clause (or 0)
// Each pass uses clauses from current active clauses and adds to next active clauses
// And then swaps the two sets
int Cnf_reasoner::bcp() {
    bool converged = false;
    bool conflict = false;
    int ncid = 0;
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
	    Clause *cp  = get_clause(cid);
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
		} else if (multi_active) {
		    continue;
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
		}
	    }
	    if (conflict) {
		report(3, "    Conflict\n");
		ncid = found_conflict(cid);
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
    return ncid;
}

// Generate set of hints for clause based on RUP validation
// Add clause as assertion
// Return ID of proof clause (or 0)
int Cnf_reasoner::rup_validate(Clause *cltp) {
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
	    Clause *cp  = get_clause(cid);
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
		} else if (multi_active) {
		    continue;
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
    int ncid = 0;
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
		Clause *clp = get_clause(hid);
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
	ncid = start_assertion(cltp);
	for (int hid : hints)
	    add_hint(hid);
	finish_command(true);
	curr_active_clauses->insert(ncid);
    }
    // Undo assignments
    pop_context();
    return ncid;
}


// Used to mark new layer in context stacks
#define CONTEXT_MARKER 0

void Cnf_reasoner::new_context() {
    context_literal_stack.push_back(CONTEXT_MARKER);
    context_clause_stack.push_back(CONTEXT_MARKER);
    report(4, "New context\n");
}

std::vector<int> *Cnf_reasoner::get_assigned_literals() {
    return &assigned_literals;
}

void Cnf_reasoner::push_assigned_literal(int lit) {
    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, already have %d as unit\n", lit, -lit);
    if (unit_literals.find(lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, it is already unit\n", lit);
    report(4, "Asserting literal %d\n", lit);
    unit_literals.insert(lit);
    assigned_literals.push_back(lit);
    context_literal_stack.push_back(lit);
}

void Cnf_reasoner::push_derived_literal(int lit, int cid) {
    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, already have derived -%d as unit\n", lit, lit);
    if (unit_literals.find(lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, it is already unit\n", lit);
    unit_literals.insert(lit);
    justifying_ids[lit] = cid;
    context_literal_stack.push_back(lit);
}

void Cnf_reasoner::push_clause(int cid) {
    //    report(4, "Deactivating clause %d\n", cid);
    context_clause_stack.push_back(cid);
}

void Cnf_reasoner::pop_context() {
    report(4, "Popping context\n");
    while (true) {
	if (context_literal_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context literal stack\n");
	int lit = context_literal_stack.back(); context_literal_stack.pop_back();
	if (lit == CONTEXT_MARKER)
	    break;
	unit_literals.erase(lit);
	if (auto fid = justifying_ids.find(lit) == justifying_ids.end()) {
	    report(4, "  Removing assertion of literal %d\n", lit);
	    assigned_literals.pop_back();
	} else {
	    justifying_ids.erase(lit);
	    report(4, "  Removing derivation of literal %d\n", lit);
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


static void copy_set(std::set<int> *dest, std::set<int> *src) {
    dest->clear();
    for (int v : *src)
	dest->insert(v);
}

void Cnf_reasoner::extract_active_clauses(std::set<int> *save_set) {
    copy_set(save_set, curr_active_clauses);
}

void Cnf_reasoner::set_active_clauses(std::set<int> *new_set) {
    copy_set(curr_active_clauses, new_set);
}


// Partition set of active clauses into subsets, each using distinct sets of variables
// Each set denoted by reference variable
// var2rvar provides a mapping from each variable to the containing set's reference variable
// rvar2cset provides a mapping from the reference variable to the set of clauses
void Cnf_reasoner::partition_clauses(std::unordered_map<int,int> &var2rvar,
				     std::unordered_map<int,std::set<int>*> &rvar2cset) {
    // Simplify clauses
    int ccid = bcp();
    if (ccid > 0)
	err(true, "BCP generated conflict on clause %d prior to partitioning\n", ccid);
    // First figure out a partitioning of the variables
    // Map from variable to representative value in its partition
    // Mapping from representative var to set of variables
    var2rvar.clear();
    std::map<int,std::unordered_set<int>*> rvar2vset;
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
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
	Clause *cp = get_clause(cid);
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
    rvar2cset.clear();
    for (auto fid : rvar2vset) {
	int rvar = fid.first;
	// Don't need variable set anymore
	delete fid.second;
	std::set<int> *cset = new std::set<int>;
	rvar2cset[rvar] = cset;
    }
    // Assign clauses to sets
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	for (int i = 0; i < cp->length(); i++) {
	    int lit = (*cp)[i];
	    int var = IABS(lit);
	    auto fid = var2rvar.find(var);
	    if (fid == var2rvar.end())
		continue;
	    int rvar = fid->second;
	    std::set<int> *cset = rvar2cset.find(rvar)->second;
	    cset->insert(cid);
	    break;
	}
    }
}

Cnf_reduced *Cnf_reasoner::extract_cnf() {
    Cnf_reduced *rcp = new Cnf_reduced();
    rcp->delete_files = delete_files;
    for (int cid : *curr_active_clauses) {
	Clause *np = get_clause(cid);	
	rcp->add_clause(np, unit_literals, cid);
    }
    return rcp;
}

// Run SAT solver on reduced set of clauses as part of effort to validate literal lit.
// Incorporate generated conflict proof into larger proof
// Return ID of conflict clause
int Cnf_reasoner::reduce_run(int lit) {
    int ncid;
    Cnf_reduced *rcp = extract_cnf();
    if (use_drat) {
	if (rcp->run_hinting_solver()) {
	    const char *fname = rcp->get_file_name();
	    pwriter->comment("Adding proof clauses from SAT solver running on file %s to validate literal %d", fname, lit);
	    int pcount = 0;
	    int start_id = clause_count() + proof_clauses.size() + 1;
	    while (true) {
		Clause *php = rcp->get_proof_hint(start_id);
		Clause *pnp = rcp->get_proof_clause(&assigned_literals);
		if (pnp == NULL)
		    break;
		pcount++;
		ncid = start_assertion(pnp);
		// Add extra information about unit literals
		for (int ulit : unit_literals) {
		    auto fid = justifying_ids.find(ulit);
		    if (fid != justifying_ids.end())
			add_hint(fid->second);
		}
		add_hints(php);
		finish_command(true);
		delete php;
	    }
	    pwriter->comment("End of proof clauses from SAT solver");
	}
    } else {
	// Want to keep track of range of clauses
	int first_ncid = 0;
	if (rcp->run_solver()) {
	    const char *fname = rcp->get_file_name();
	    pwriter->comment("Adding proof clauses from SAT solver running on file %s to validate literal %d", fname, lit);
	    int pcount = 0;
	    while (true) {
		Clause *pnp = rcp->get_proof_clause(&assigned_literals);
		if (pnp == NULL)
		    break;
		pcount++;
		ncid = rup_validate(pnp);
		if (first_ncid == 0)
		    first_ncid = ncid;
		if (ncid == 0) {
		    err(false, "SAT solver running on file %s failed to validate proof clause #%d while validating literal %d\n",
			fname, pcount, lit);
		    if (verblevel >= 3)
			pnp->show();
		}
	    }
	    pwriter->comment("End of proof clauses from SAT solver");
	}
	// The clauses used in generating this proof are no longer needed
	for (int cid = first_ncid; cid <= ncid; cid++)
	    curr_active_clauses->erase(cid);
    }
    if (ncid > 0) {
	report(5, "Validated literal %d.  Used SAT solver\n", lit);
    }
    delete rcp;
    return ncid;
}

// Justify that literal holds.  Return ID of justifying clause
// Mode specifies different levels of effort
int Cnf_reasoner::validate_literal(int lit, validation_mode_t mode) {
    report(5, "Attempting to Validate literal %d\n", lit);
    auto fid = justifying_ids.find(lit);
    if (fid != justifying_ids.end()) {
	report(5, "Validated literal %d.  Already unit\n", lit);
	return fid->second;
    }
    if (unit_literals.find(-lit) != unit_literals.end()) {
	report(5, "Validating literal %d.  BUT %d is unit\n", lit, -lit);
	return 0;
    }

    int ncid = 0;
    new_context();
    push_assigned_literal(-lit);
    if (mode != MODE_SAT) {
	ncid = bcp();
	if (ncid > 0)
	    report(5, "Validated literal %d.  Justified by BCP\n", lit);
    }
    if (ncid == 0 && mode != MODE_BCP) {
	ncid = reduce_run(lit);
    }
    pop_context();

    if (ncid == 0) 
	report(5, "Couldn't validate literal %d %s SAT solver\n", lit, mode == MODE_BCP ? "without" : "with");
    else
	push_derived_literal(lit, ncid);

    return ncid;
}

// Justify that set of literals hold.
// Justifying clauses IDs are then loaded into jids vector
void Cnf_reasoner::validate_literals(std::vector<int> &lits, std::vector<int> &jids, int *xvar_counter) {
    jids.resize(lits.size());
    validation_mode_t mode = multi_literal ? MODE_BCP : MODE_FULL;
    std::vector<int> deferred_pos;
    // First pass: 
    // In standard mode, validate each literal separately
    // In multi_literal mode, look for easy cases.  Defer the rest
    for (int i = 0; i < lits.size(); i++) {
	int lit = lits[i];
	int jid = validate_literal(lit, mode);
	jids[i] = jid;
	if (jid == 0) {
	    deferred_pos.push_back(i);
	}
    }

    if (deferred_pos.size() == 0) {
	return;
    }

    if (deferred_pos.size() == 1) {
	// Handle as single literal
	int  i = deferred_pos[0];
	jids[i] = validate_literal(lits[i], MODE_FULL);
	return;
    }
    int xvar = ++*xvar_counter;
    int nleft = deferred_pos.size();
    ilist args = ilist_new(nleft);
    for (int i : deferred_pos)
	args = ilist_push(args, lits[i]);
    int defining_cid = start_and(xvar, args);
    finish_command(false);
    document_and(defining_cid, xvar, args);
    // Activate conjunction definition
    curr_active_clauses->insert(defining_cid);
    pwriter->comment("Handle %d/%d literals with SAT solver to validate extension variable %d", nleft, lits.size(), xvar);
    report(3, "Handle %d/%d literals with SAT solver to validate extension variable %d\n", nleft, lits.size(), xvar);
    int ncid = validate_literal(xvar, MODE_FULL);
    if (ncid == 0) {
	err(false, "Couldn't validate literal %d representing conjunction of %d literals\n", xvar, nleft);
    }
    // Final pass: Target units should be unit or provable with BCP
    for (int offset = 0; offset < nleft; offset++) {
	int i = deferred_pos[offset];
	int lit = lits[i];
	int jid = quick_validate_literal(lit, ncid, defining_cid+offset+1);
	jids[i] = jid;
    }
    pwriter->comment("Justifications of %d literals completed", nleft);
    curr_active_clauses->erase(defining_cid);
}


void Cnf_reasoner::delete_assertions() {
    // Don't want last one
    pwriter->comment("Delete all but final asserted clause");
    bool remove = false;
    while (deletion_stack.size() > 0) {
	std::vector<int> *dvp = deletion_stack.back();
	if (remove)
	    pwriter->clause_deletion(dvp);
	remove = true;
	delete dvp;
	deletion_stack.pop_back();
    }
}
