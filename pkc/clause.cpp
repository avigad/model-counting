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
    allow_flush = false;
}


// Use file name to construct root for temporary names
void File_manager::set_root(const char *fname) {
    // Trim any leading path directories
    int lpos = strlen(fname);
    while (lpos >= 0 && fname[lpos] != '/')
	lpos--;
    lpos++;
    snprintf(buf, strlen(fname) + 10, "zzzz-%s", fname+lpos);
    // Chop off extension
    int rpos = strlen(buf);
    while (rpos >= 0 && buf[rpos] != '.')
	rpos--;
    if (rpos > 0)
	buf[rpos] = '\0';
    root = archive_string(buf);
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
    if (!allow_flush)
	return;
    for (const char *fname : names) {
	if (remove(fname) != 0)
	    err(false, "Attempt to delete file %s failed.  Error code = %d\n", fname, errno);
	free((void *) fname);
    }
    names.clear();
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
    cmap_offsets = NULL;
    cmap_lists = NULL;
}

// Process comment, looking additional data variables & weights
// Return last character
static void process_comment(FILE *infile, std::unordered_set<int> &data_variables , std::unordered_map<int,q25_ptr> &input_weights) {
    char buf[50];
    int len;
    if (find_string_token(infile, buf, 50, &len) && len == 1 && strncmp(buf, "p", 1) == 0
	&& find_string_token(infile, buf, 50, &len)) {
	if (len == 4 && strncmp(buf, "show", 4) == 0) {
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
	else if (len == 6 && strncmp(buf, "weight", 6) == 0) {
	    int lit = 0;
	    if (fscanf(infile, "%d", &lit) != 1) {
		err(false, "Couldn't read weight literal (skipping)\n");
		skip_line(infile);
		return;
	    }
	    find_token(infile);
	    q25_ptr wt = q25_read(infile);
	    if (!q25_is_valid(wt)) {
		err(false, "Couldn't read weight for literal %d (skipping)\n", lit);
		skip_line(infile);
		return;
	    }
	    input_weights[lit] = wt;
	    int zero;
	    if (fscanf(infile, "%d", &zero) != 1 || zero != 0) {
		err(false, "Couldn't read terminating zero in weight declaration for literal %d (accepting weight)\n", lit);
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
	    process_comment(infile, data_variables, input_weights);
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
		process_comment(infile, data_variables, input_weights);
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
	    process_comment(infile, data_variables, input_weights);
    }
    arx = finish_build(varx);
    // If no data variables declared, assume all input variables are data variables
    if (data_variables.size() == 0) {
	for (int v = 1; v <= variable_count(); v++)
	    data_variables.insert(v);
    }
    build_cmap();
    incr_count_by(COUNT_INPUT_CLAUSE, clause_count());
    incr_count_by(COUNT_INPUT_VAR, variable_count());
    incr_count_by(COUNT_DATA_VAR, data_variables.size());
}

void Cnf::import_archive(cnf_archive_t iarx) {
    arx = iarx;
}

Cnf::~Cnf() {
    arx = NULL;
    for (auto iter : input_weights)
	q25_free(iter.second);
    delete cmap_offsets;
    delete cmap_lists;
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
    fmgr.flush();
    return rc == 10 || (rc >> 8) == 10;
}

void Cnf::find_tautologies(std::unordered_set<int> &tauts) {
    tauts.clear();
    std::unordered_set<int> lits;
    for (int cid = 1; cid <= clause_count(); cid++) {
	lits.clear();
	int len = clause_length(cid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = get_literal(cid, lid);
	    if (lits.find(-lit) !=  lits.end())
		tauts.insert(cid);
	    lits.insert(lit);
	}
    }
}

// Creating and working with cmap, an inverse map from each projection variable
// to the clauses containing it.

void Cnf::build_cmap() {
    // For each projection variable, list of clauses containing it
    // Lists for data variables stay empty
    // Indexed by variable - 1

    // Will need degree entry for each projection variable
    int mcount = variable_count() - data_variables.size();
    std::unordered_map<int,std::vector<int>> tmp_cmap;
    for (int cid = 1; cid <= clause_count(); cid++) {
	int len = clause_length(cid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = get_literal(cid, lid);
	    int var = IABS(lit);
	    if (data_variables.find(var) == data_variables.end()) {
		tmp_cmap[var-1].push_back(cid);
		mcount++;
	    }
	}
    }
    cmap_offsets = new int[variable_count()];
    cmap_lists = new int[mcount];
    // Fill it up
    int next_offset = 0;
    for (int var = 1; var <=  variable_count(); var++) {
	if (data_variables.find(var) == data_variables.end()) {
	    cmap_offsets[var-1] = next_offset;
	    cmap_lists[next_offset++] = tmp_cmap[var-1].size();
	    for (int cid : tmp_cmap[var-1])
		cmap_lists[next_offset++] = cid;
	} else
	    cmap_offsets[var-1] = -1;
    }
    report(2, "Inverse clause map contains %d clause IDs\n",
	   mcount - (variable_count() - data_variables.size()));
}

// Accessing cmap entries
int Cnf::get_cmap_clause_count(int var) {
    int offset = cmap_offsets[var-1];
    if (offset < 0)
	return 0;
    return cmap_lists[offset];
}

int Cnf::get_cmap_cid(int var, int index) {
    int offset = cmap_offsets[var-1];
    if (offset < 0)
	return 0;
    return cmap_lists[offset+index+1];
}

Clausal_reasoner::Clausal_reasoner(Cnf *icnf) {
    cnf = icnf;
    // Set up active clauses
    has_conflict = false;
    std::unordered_set<int> tauts;
    cnf->find_tautologies(tauts);
    for (int cid = 1; cid <= cnf->clause_count(); cid++)
	if (tauts.find(cid) == tauts.end())
	    active_clauses.insert(cid);
    new_context();
    bcp_step_limit = 0; // Unlimited
    trace_variable = 0;
    context_level = 0;
    use_local_clauses = false;
}

Clausal_reasoner::~Clausal_reasoner() {
}

bool Clausal_reasoner::skip_clause(int cid) {
    int len = cnf->clause_length(cid);    
    for (int lid = 0; lid < len; lid++) {
	int lit = cnf->get_literal(cid, lid);
	if (exit_clause(lit))
	    return true;
    }
    return false;
}


void Clausal_reasoner::new_context() {
    unit_trail.push_back({0,false,false});
    uquant_trail.push_back(0);
    clause_trail.push_back(0);
    context_level++;
    report(3, "Starting context level %d\n", context_level);
    if (trace_variable != 0) {
	if (quantified_variables.find(trace_variable) != quantified_variables.end())
	    report(3, "   %d quantified\n", trace_variable);
	for (int phase = -1; phase <= 1; phase +=2) {
	    int lit = phase * trace_variable;
	    if (unit_literals.find(lit) != unit_literals.end()) {
		bool is_bcp = bcp_unit_literals.find(lit) != bcp_unit_literals.end();
		report(3, "   %d is %s unit literal\n", lit, is_bcp ? "BCP" : "assigned");
	    }
	}
    }
}

void Clausal_reasoner::pop_context() {
    has_conflict = false;

    while (true) {
	utrail_ele ute = unit_trail.back();
	int lit = ute.lit;
	int var = IABS(lit);
	unit_trail.pop_back();
	if (lit == 0)
	    break;
	bool is_unit = unit_literals.find(lit) != unit_literals.end();
	bool is_bcp_unit = bcp_unit_literals.find(lit) != bcp_unit_literals.end();
	//	report(4, "Popped UTE %d, unit %s --> %s, bcp_unit = %s --> %s\n",
	//	       lit,
	//	       is_unit ? "true" : "false",
	//	       ute.was_unit ? "true" : "false",
	//	       is_bcp_unit ? "true" : "false",
	//	       ute.was_bcp_unit ? "true" : "false");
	if (is_unit != ute.was_unit) {
	    if (is_unit) {
		unit_literals.erase(lit);
		report(var == trace_variable ? 1 : 4, "Context level %d: Unassigning unit literal %d\n", context_level, lit);
	    } else {
		unit_literals.insert(lit);
		report(var == trace_variable ? 1 : 4, "Context level %d: Reassigning unit literal %d\n", context_level, lit);

	    }
	}
	if (is_bcp_unit != ute.was_bcp_unit) {
	    if (is_bcp_unit) {
		bcp_unit_literals.erase(lit);
		report(var == trace_variable ? 1 : 4, "Context level %d: Unassigning BCP unit literal %d\n", context_level, lit);
	    } else {
		bcp_unit_literals.insert(lit);
		report(var == trace_variable ? 1 : 4, "Context level %d: Reassigning BCP unit literal %d\n", context_level, lit);
	    }
	}
    }
    while (true) {
	int var = uquant_trail.back();
	uquant_trail.pop_back();
	if (var ==  0)
	    break;
	quantified_variables.erase(var);
    }
    while (true) {
	int cid = clause_trail.back();
	clause_trail.pop_back();
	if (cid == 0)
	    break;
	active_clauses.insert(cid);
    }
    report(3, "Completing context level %d\n", context_level);
    if (trace_variable != 0) {
	if (quantified_variables.find(trace_variable) != quantified_variables.end())
	    report(3, "   %d quantified\n", trace_variable);
	for (int phase = -1; phase <= 1; phase +=2) {
	    int lit = phase * trace_variable;
	    if (unit_literals.find(lit) != unit_literals.end()) {
		bool is_bcp = bcp_unit_literals.find(lit) != bcp_unit_literals.end();
		report(3, "   %d is %s unit literal\n", lit, is_bcp ? "BCP" : "assigned");
	    }
	}
    }
    context_level--;
}

// Mark clause for deactivation once iterator completes
// Clause is no longer considered part of clausal state
void Clausal_reasoner::deactivate_clause(int cid) {
    active_clauses.erase(cid);
    clause_trail.push_back(cid);
}

void Clausal_reasoner::deactivate_clauses(std::vector<int> &remove) {
    for (int cid : remove)
	deactivate_clause(cid);
}


// Mark clause for deactivation once iterator completes
// Its unit clause is no longer considered part of clausal state
void Clausal_reasoner::deactivate_bcp_unit_literal(int lit) {
    bcp_unit_literals.erase(lit);
    unit_trail.push_back({lit,true,true});
    int var = IABS(lit);
    report(var == trace_variable ? 1 : 4, "Context level %d: Deactivating BCP unit literal %d\n", context_level, lit);
}

void Clausal_reasoner::deactivate_bcp_unit_literals(std::vector<int> &remove) {
    for (int lit : remove)
	deactivate_bcp_unit_literal(lit);
}

void Clausal_reasoner::trigger_conflict() {
    report(3, "Conflict triggered\n");
    has_conflict = true;
    return;
}

void Clausal_reasoner::assign_literal(int lit, bool bcp) {
    if (lit == 0) {
	err(true, "Can't assign literal %d\n", lit);
    }
    int var = IABS(lit);
    bool was_unit = unit_literals.find(lit) != unit_literals.end();
    bool was_bcp_unit = bcp_unit_literals.find(lit) != bcp_unit_literals.end();

    // Should not be a quantified variable
    if (quantified_variables.find(var) != quantified_variables.end()) {
	err(false, "Attempt to assign literal %d even though variable already quantified\n", lit);
	lprintf("Currently quantified variables:\n");
	for (int qvar : quantified_variables) {
	    lprintf(" %d", qvar);
	}
	lprintf("\n");
	err(true, "Fatal\n");
    }

    if (unit_literals.find(-lit) != unit_literals.end()) {
	int var = IABS(lit);
	report(var == trace_variable ? 1 : 4, "Context level %d: Assigning literal %d by %s triggering conflict\n",
	       context_level, lit, bcp ? "BCP" : "assignment");
	trigger_conflict();
    }
    else if (bcp) {
	if (was_unit)
	    err(false, "Attempt to set literal %d by BCP that is unit\n", lit);
	report(var == trace_variable ? 1 : 4, "Context level %d: Setting literal %d by BCP\n", context_level, lit);
	unit_literals.insert(lit);
	bcp_unit_literals.insert(lit);
	unit_trail.push_back({lit,was_unit,was_bcp_unit});
    } else {
	if (was_bcp_unit)
	    bcp_unit_literals.erase(lit);
	else if (was_unit)
	    err(false, "Attempt to assign literal %d that is already assigned\n", lit);
	report(var == trace_variable ? 1 : 4, "Context level %d: Setting literal %d by assignment (was_bcp = %s)\n", context_level, lit,
	       was_bcp_unit ? "true" : "false");
	unit_literals.insert(lit);
	unit_trail.push_back({lit,was_unit,was_bcp_unit});
    }
}

void Clausal_reasoner::quantify(int var) {
    if (var <= 0) {
	err(true, "Can't quantify variable %d\n", var);
    }
    report(var == trace_variable ? 1 : 4, "Context level %d: Quantifying variable %d\n", context_level, var);
    for (int phase = -1; phase <= 1; phase += 2) {
	int lit = phase * var;
	if (bcp_unit_literals.find(lit) != unit_literals.end())
	    deactivate_bcp_unit_literal(lit);
	else if (unit_literals.find(lit) != unit_literals.end())
		err(false, "Attempt to quantify variable %d, but literal %d already assigned\n", var, lit);
    }
    quantified_variables.insert(var);
    uquant_trail.push_back(var);
}

// Expand set of variables to include those that co-occur in clauses with given variables
// May require multiple iterations
void Clausal_reasoner::expand_partition(std::unordered_set<int> &vset) {
    int added = true;
    int osize = vset.size();
    std::vector<int> others;
    while (added) {
	added = false;
	for (int cid : active_clauses) {
	    if (skip_clause(cid))
		continue;
	    bool existing = false;
	    others.clear();
	    int len = cnf->clause_length(cid);
	    for (int lid = 0; lid < len; lid++) {
		int lit = cnf->get_literal(cid, lid);
		if (skip_literal(lit))
		    continue;
		int var = IABS(lit);
		if (vset.find(var) == vset.end())
		    others.push_back(var);
		else
		    existing = true;
	    }
	    if (existing && others.size() > 0) {
		added = true;
		for (int var : others)
		    vset.insert(var);
	    }
	}
    }
    int nsize = vset.size();
    if (nsize > osize)
	report(3, "  Partition variables expanded from %d to %d\n", osize, nsize);
}


// Filter clauses to contain only those with variables in vset
void Clausal_reasoner::partition(std::unordered_set<int> & vset) {
    // Make sure that have all variables in partition
    expand_partition(vset);
    std::vector<int> remove;
    int ocsize = active_clauses.size();
    int obsize = bcp_unit_literals.size();
    for (int cid : active_clauses) {
	if (skip_clause(cid))
	    continue;
	int len = cnf->clause_length(cid);
	bool include = false;
	for (int lid = 0; !include && lid < len; lid++) {
	    int lit = cnf->get_literal(cid, lid);
	    if (skip_literal(lit))
		continue;
	    int var = IABS(lit);
	    include = vset.find(var) != vset.end();
	}
	if (!include)
	    remove.push_back(cid);
    }
    deactivate_clauses(remove);
    remove.clear();
    for (int lit : bcp_unit_literals) {
	if (vset.find(lit) == vset.end())
	    remove.push_back(lit);
    }
    deactivate_bcp_unit_literals(remove);
    report(3, "  Partition %d/%d active clauses, %d/%d BCP unit literals\n",
	   active_clauses.size(), ocsize,
	   bcp_unit_literals.size(), obsize);
}


// A hack to enable direct KC of simple formulas.
// Applies only when KC can be expressed as product of clauses over distinct variables
// If condition holds, fill up vector with zero-separated sequences of literals
bool Clausal_reasoner::check_simple_kc(std::vector<int> &clause_chunks) {
    clause_chunks.clear();
    std::unordered_set<int> vset;
    for (int lit : bcp_unit_literals)
	vset.insert(IABS(lit));
    bool ok = true;
    for (int cid : active_clauses) {
	if (skip_clause(cid))
	    continue;
	int len = cnf->clause_length(cid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = cnf->get_literal(cid, lid);
	    if (skip_literal(lit))
		continue;
	    int var = IABS(lit);
	    if (vset.find(var) != vset.end()) {
		ok = false;
		break;
	    }
	    vset.insert(var);
	    clause_chunks.push_back(lit);
	}
	clause_chunks.push_back(0);
    }
    if (ok) {
	for (int lit : bcp_unit_literals) {
	    clause_chunks.push_back(lit);
	    clause_chunks.push_back(0);
	}
    }
    return ok;
}

// Return TAUTOLOGY, CONFLICT, propagated unit, or zero
int Clausal_reasoner::propagate_clause(int cid) {
    int len = cnf->clause_length(cid);
    int result = CONFLICT;
    for (int lid = 0; lid < len; lid++) {
	int lit = cnf->get_literal(cid, lid);
	if (exit_clause(lit)) {
	    result = TAUTOLOGY;
	    break;
	}
	if (skip_literal(lit))
	    continue;
	if (result == CONFLICT)
	    result = lit;
	else
	    result = 0;
    }
    return result;
}


// Return true if unpropagated unit literal remains.
// Update next active clauses
bool Clausal_reasoner::unit_propagate() {
    bool new_unit = false;
    std::vector<int> remove;
    for (int cid : use_local_clauses ? local_clauses : active_clauses) {
	int rval = propagate_clause(cid);
	if (rval == CONFLICT) {
	    report(3, "Context level %d: Unit propagation finds conflict at clause #%d\n", context_level, cid);
	    has_conflict = true;
	    break;
	}
	if (rval == 0)
	    continue;
	if (rval == TAUTOLOGY) {
	    remove.push_back(cid);
	    continue;
	}
	// Derived unit literal
	assign_literal(rval, true);	    
	remove.push_back(cid);
	new_unit = true;
    }
    if (has_conflict) {
	trigger_conflict();
	new_unit = false;
    } else {
	if (use_local_clauses) {
	    for (int cid : remove)
		local_clauses.erase(cid);
	} else
	    deactivate_clauses(remove);
    }
    return new_unit;
}

void Clausal_reasoner::bcp(bool full) {
    for (int step = 1; !has_conflict && (full || bcp_step_limit == 0 || step < bcp_step_limit); step++) {
	if (!unit_propagate())
	    break;
    }
}

int Clausal_reasoner::current_clause_count()  { 
    if (has_conflict)
	return 1;
    else if (use_local_clauses)
	return local_clauses.size() + bcp_unit_literals.size();
    else
	return active_clauses.size() + bcp_unit_literals.size();
}

cnf_archive_t Clausal_reasoner::extract() {
    std::vector<int> varx;
    bcp(true);
    start_build(varx, cnf->variable_count(), current_clause_count());
    int ncid = 0;
    if (has_conflict)
	err(true, "Attempt to extract unsatisfiable CNF\n");
    // Put in the derived unit literals
    for (int ulit : bcp_unit_literals) {
	new_clause(varx, ++ncid);
	add_literal(varx, ulit);
    }
    for (int ocid : use_local_clauses ? local_clauses : active_clauses) {
	if (skip_clause(ocid))
	    continue;
	new_clause(varx, ++ncid);
	int len = cnf->clause_length(ocid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = cnf->get_literal(ocid, lid);
	    if (!skip_literal(lit))
		add_literal(varx, lit);
	}
    }
    return finish_build(varx);
}

bool Clausal_reasoner::write(FILE *outfile) {
    bcp(true);
    if (has_conflict)
	err(true, "Attempt to write unsatisfiable CNF\n");
    fprintf(outfile, "p cnf %d %d\n", cnf->variable_count(), current_clause_count());
    // Put in the derived unit literals
    for (int ulit : bcp_unit_literals) 
	fprintf(outfile, "%d 0\n", ulit);
    for (int ocid : use_local_clauses ? local_clauses : active_clauses) {
	if (skip_clause(ocid)) {
	    err(false, "Found tautological clause #%d\n", ocid);
	    continue;
	}
	int len = cnf->clause_length(ocid);
	for (int lid = 0; lid < len; lid++) {
	    int lit = cnf->get_literal(ocid, lid);
	    if (!skip_literal(lit))
		fprintf(outfile, "%d ", lit); 
	}
	fprintf(outfile, "0\n");
    }
    return true;
}

bool Clausal_reasoner::is_satisfiable() {
    bcp(true);
    if (has_conflict)
	return false;
    if (active_clauses.size() <= 1)
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

bool Clausal_reasoner::is_locally_satisfiable(int var) {
    // See if local set of clauses unsatisfiable in current context
    int len = cnf->get_cmap_clause_count(var);
    if (len == 0) {
	err(false, "Trying to do local satisfiability with data variable %d\n", var);
	return is_satisfiable();
    }
    use_local_clauses = true;
    local_clauses.clear();
    for (int i = 0; i < len; i++) {
	int cid = cnf->get_cmap_cid(var, i);
	if (active_clauses.find(cid) != active_clauses.end()) {
	    local_clauses.insert(cid);
	}
    }
    report(3, "Computing local satisfiability for variable %d over %d clauses\n", var, local_clauses.size());
    if (verblevel >= 3) {
	lprintf("  IDs:");
	for (int cid : local_clauses)
	    lprintf(" %d", cid);
	lprintf("\n");
    }
    bool result = is_satisfiable();
    // Undo
    use_local_clauses = false;
    return result;
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
