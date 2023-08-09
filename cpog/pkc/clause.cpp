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

// File management
// Share instance of file manager globally
File_manager fmgr;

File_manager::File_manager() {
    root = archive_string("zzzz-temporary");
    sequence_number = 1000000;
    buflen = 1000;
    buf = (char *) malloc(buflen);
}

// Use file name to construct root for temporary names
void File_manager::set_root(const char *fname) {
    strncpy(buf, fname, strlen(fname));
    // Chop off extension
    int pos = strlen(fname)-1;
    while (pos >= 0 && buf[pos] != '.')
	pos--;
    if (pos > 0) {
	snprintf(buf+pos, 5, "-xxxxx");
	root = archive_string(buf);
    }
}

const char *File_manager::build_name(const char *extension, bool new_sequence) {
    if (new_sequence)
	sequence_number++;
    snprintf(buf, buflen, "%s-%d.%s", root, sequence_number, extension);
    const char *result = archive_string(buf);
    names.push_back(result);
    return result;
}

void File_manager::flush() {
    for (const char *fname : names) {
	if (remove(fname) != 0)
	    err(false, "Attempt to delete file %s failed.  Error code = %d\n", fname, errno);
	free((void *) fname);
    }
}

// Put literals in ascending order of the variables
static bool abs_less(int x, int y) {
    return IABS(x) < IABS(y);
}


static int skip_line(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return c;
    }
    return c;
}

// Skip over spaces, newlines, etc., until find something interesting
// Return last character encountered
static int find_token(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (!isspace(c)) {
	    ungetc(c, infile);
	    break;
	}
    }
    return c;
}

// Read string token:
// Skip over spaces.
// Read contiguous non-space characters and store in dest.
// Set len to number of characters read.
// Return false if EOF encountered without getting string
static bool find_string_token(FILE *infile, char *dest, int maxlen, int *len) {
    int c;
    int rlen = 0;
    while ((c = getc(infile)) != EOF && rlen < maxlen-1) {
	if (isspace(c)) {
	    if (rlen > 0) {
		// Past token
		ungetc(c, infile);
		break;
	    }
	} else {
	    *(dest+rlen) = c;
	    rlen++;
	}
    }
    *(dest+rlen) = '\0';
    *len = rlen;
    return (c != EOF);
}

// Tools to enable constructing CNF representations
static void start_build(std::vector<int> &varx, int nvar, int nclause) {
    varx.clear();
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

// Process comment, looking additional data variables
// Return last character
static void process_comment(FILE *infile, std::unordered_set<int> &data_variables) {
    char buf[50];
    int len;
    if (find_string_token(infile, buf, 50, &len) && len == 1 && strncmp(buf, "p", 1) == 0
	&& find_string_token(infile, buf, 50, &len) && len == 4 && strncmp(buf, "show", 4) == 0) {
	int var = -1;
	while (var != 0) {
	    if (fscanf(infile, "%d", &var) != 1) {
		err(false, "Couldn't read data variable\n");
		break;
	    } else if (var != 0) {
		data_variables.insert(var);
	    }
	}
    }
    skip_line(infile);
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
    // Clear set of data variables
    data_variables.clear();
    // Look for CNF header
    while ((c = getc(infile)) != EOF) {
	if (isspace(c)) 
	    continue;
	if (c == 'c') {
	    process_comment(infile, data_variables);
	    continue;
	}
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
	bool starting_clause = true;
	while (true) {
	    int lit;
	    int c = find_token(infile);
	    if (c == EOF) {
		err(false, "Unexpected end of file\n");
		return;
	    } else if (c == 'c' && starting_clause) {
		c = getc(infile);
		process_comment(infile, data_variables);
		continue;
	    }
	    else if (fscanf(infile, "%d", &lit) != 1) {
		err(false, "Couldn't find literal or 0\n");
		return;
	    }
	    if (lit == 0)
		break;
	    else 
		add_literal(varx, lit);
	    starting_clause = false;
	}
    }
    while ((c = getc(infile)) != EOF) {
	if (isspace(c)) 
	    continue;
	if (c == 'c') 
	    process_comment(infile, data_variables);
    }
    arx = finish_build(varx);
    // If no data variables declared, assume all input variables are data variables
    if (data_variables.size() == 0) {
	for (int v = 1; v <= variable_count(); v++)
	    data_variables.insert(v);
    }
    incr_count_by(COUNT_INPUT_CLAUSE, clause_count());
    incr_count_by(COUNT_INPUT_VAR, variable_count());
    incr_count_by(COUNT_DATA_VAR, data_variables.size());

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

bool Cnf::is_satisfiable() {
    double start = tod();
    FILE *pipe = popen("cadical -q > /dev/null", "w");
    if (!write(pipe)) {
	err(false, "Couldn't open pipe to cadical\n");
	return false;
    }
    int rc = pclose(pipe);
    double elapsed = tod() - start;
    incr_timer(TIME_SAT, elapsed);
    incr_count(COUNT_SAT_CALL);
    incr_histo(HISTO_SAT_CLAUSES, clause_count());
    return rc == 10 || (rc >> 8) == 10;
}


Clausal_reasoner::Clausal_reasoner(Cnf *icnf) {
    cnf = icnf;
    // Set up active clauses
    has_conflict = false;
    curr_active_clauses = new std::set<int>;
    next_active_clauses = new std::set<int>;
    for (int cid = 1; cid <= cnf->clause_count(); cid++)
	curr_active_clauses->insert(cid);
    new_context();
    bcp_step_limit = 0; // Unlimited
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
	bcp_unit_literals.erase(lit);
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
	curr_active_clauses->insert(cid);
    }
}

void Clausal_reasoner::deactivate_clause(int cid) {
    deactivated_clauses.push_back(cid);
}


void Clausal_reasoner::assign_literal(int lit, bool bcp) {
    int var = IABS(lit);
    unit_literals.insert(lit);
    if (bcp)
	bcp_unit_literals.insert(lit);
    unit_trail.push_back(lit);
    if (unit_literals.find(lit) != unit_literals.end()) {
	//	err(false, "Attempt to assign literal %d that is unit\n", lit);
    } else if (unit_literals.find(-lit) != unit_literals.end()) {
	//	err(false, "Attempt to assign literal %d for which its negation is unit\n", lit);
	has_conflict = true;
	for (int cid : *curr_active_clauses)
	    deactivate_clause(cid);
	curr_active_clauses->clear();
	
    } else if (quantified_variables.find(var) != quantified_variables.end()) {
	//	err(false, "Attempt to assign literal %d even though variable quantified\n", lit);
    }
}

void Clausal_reasoner::quantify(int var) {
    if (unit_literals.find(var) != unit_literals.end()) {
	//	err(false, "Attempt to quantify variable %d, but literal %d is unit\n", var, var);
    } else if (unit_literals.find(-var) != unit_literals.end()) {
	//	err(false, "Attempt to quantify variable %d, but literal %d is unit\n", var, -var);
    } else if (quantified_variables.find(var) != quantified_variables.end()) {
	err(false, "Attempt to quantify variable %d even already quantified\n", var);
    } else {
	quantified_variables.insert(var);
	uquant_trail.push_back(var);
    }
}

// Expand set of variables to include those that co-occur in clauses with given variables
// May require multiple iterations
void Clausal_reasoner::expand_partition(std::unordered_set<int> &vset) {
    int added = true;
    std::vector<int> others;
    while (added) {
	added = false;
	for (int cid : *curr_active_clauses) {
	    bool existing = false;
	    others.clear();
	    int len = cnf->clause_length(cid);
	    for (int lid = 0; lid < len; lid++) {
		int lit = cnf->get_literal(cid, lid);
		if (unit_literals.find(-lit) != unit_literals.end())
		    continue;
		int var = IABS(lit);
		if (vset.find(var) == vset.end())
		    others.push_back(var);
		else
		    existing = true;
	    }
	    if (!existing || others.size() == 0)
		continue;
	    added = true;
	    for (int var : others)
		vset.insert(var);
	}
    }
}


// Filter clauses to contain only those with variables in vset
void Clausal_reasoner::partition(std::unordered_set<int> & vset) {
    // Make sure that have all variables in partition
    expand_partition(vset);
    next_active_clauses->clear();
    for (int cid : *curr_active_clauses) {
	int len = cnf->clause_length(cid);
	int include = false;
	for (int lid = 0; !include && lid < len; lid++) {
	    int lit = cnf->get_literal(cid, lid);
	    int var = IABS(lit);
	    if (unit_literals.find(-lit) != unit_literals.end())
		continue;
	    include = vset.find(var) != vset.end();
	}
	if (include)
	    next_active_clauses->insert(cid);
	else
	    deactivate_clause(cid);
    }
    auto tmp = curr_active_clauses;
    curr_active_clauses = next_active_clauses;
    next_active_clauses = tmp;
}

void Clausal_reasoner::analyze_variables(bool &only_data, bool &only_project) {
    only_data = true;
    only_project = true;
    for (int cid : *curr_active_clauses) {
	if (!only_data && !only_project)
	    return;
	int len = cnf->clause_length(cid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = cnf->get_literal(cid, lid);
	    if (unit_literals.find(-lit) != unit_literals.end())
		continue;
	    int var = IABS(lit);
	    if (cnf->data_variables.find(var) == cnf->data_variables.end())
		only_data = false;
	    else
		only_project = false;
	}
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
	if (has_conflict) {
	    deactivate_clause(cid);
	    continue;
	}
	int rval = propagate_clause(cid);
	if (rval == CONFLICT) {
	    // Reduce to single conflict clause
	    has_conflict = true;
	    for (int ccid : *next_active_clauses)
		deactivate_clause(ccid);
	    next_active_clauses->clear();
	    new_unit = false;
	} else if (rval == 0) {
	    next_active_clauses->insert(cid);
	} else if (rval == TAUTOLOGY) {
	    deactivate_clause(cid);
	} else {
	    // Derived unit literal
	    assign_literal(rval, true);
	    deactivate_clause(cid);
	    new_unit = true;
	}
    }
    auto tmp = curr_active_clauses;
    curr_active_clauses = next_active_clauses;
    next_active_clauses = tmp;
    return new_unit;
}

bool Clausal_reasoner::bcp(bool full) {
    for (int step = 1; full || bcp_step_limit == 0 || step < bcp_step_limit; step++) {
	if (!unit_propagate())
	    break;
    }
    return has_conflict;
}

cnf_archive_t Clausal_reasoner::extract() {
    std::vector<int> varx;
    start_build(varx, cnf->variable_count(), bcp_unit_literals.size() + curr_active_clauses->size());
    int ncid = 0;
    // Put in the derived unit literals
    for (int ulit : bcp_unit_literals) {
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
bool Clausal_reasoner::write(FILE *outfile) {
    fprintf(outfile, "p cnf %d %ld\n", cnf->variable_count(), bcp_unit_literals.size() + curr_active_clauses->size());
    // Put in the derived unit literals
    for (int ulit : bcp_unit_literals) 
	fprintf(outfile, "%d 0\n", ulit);
    for (int ocid : *curr_active_clauses) {
	int len = cnf->clause_length(ocid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = cnf->get_literal(ocid, lid);
	    int var = IABS(lit);
	    if (unit_literals.find(-lit) == unit_literals.end() &&
		quantified_variables.find(var) == quantified_variables.end())
		fprintf(outfile, "%d ", lit); 
	}
	fprintf(outfile, "0\n");
    }
    return true;
}


bool Clausal_reasoner::is_satisfiable() {
    if (has_conflict)
	return false;
    if (curr_active_clauses->size() <= 1)
	return true;
    double start = tod();
    FILE *pipe = popen("cadical -q > /dev/null", "w");
    if (!write(pipe)) {
	err(false, "Couldn't open pipe to cadical\n");
	return false;
    }
    int rc = pclose(pipe);
    double elapsed = tod() - start;
    incr_timer(TIME_SAT, elapsed);
    incr_count(COUNT_SAT_CALL);
    incr_histo(HISTO_SAT_CLAUSES, current_clause_count());
    return rc == 10 || (rc >> 8) == 10;
}

void Clausal_reasoner::show_units(FILE *outfile) {
    std::vector<int> ulits;
    for (int lit : unit_literals) 
	ulits.push_back(lit);
    std::sort(ulits.begin(), ulits.end(), abs_less);
    int first = true;
    for (int lit : ulits) {
	fprintf(outfile, first ? "%d" : ", %d", lit);
	first = false;
    }
}
