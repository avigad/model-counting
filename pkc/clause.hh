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


#pragma once

// Used to convert literal to variable
#define IABS(x) ((x)<0?-(x):(x))

#define TAUTOLOGY INT_MAX
#define CONFLICT (-TAUTOLOGY)

#include <vector>
#include <set>
#include <unordered_set>
#include <stdio.h>
#include "q25.h"

// Manage temporary files
class File_manager {
private:
    // Names of files generated
    int buflen;
    char *buf;
    std::vector<const char *> names;
    const char *root;
    int sequence_number;
    bool allow_flush;

public:
    File_manager();
    void enable_flush() { allow_flush = true; }
    void set_root(const char *fname);
    const char *build_name(const char *extension, bool new_sequence);
    void flush();
};

extern File_manager fmgr;

// Base data type for storing CNF
typedef int *cnf_archive_t;

class Cnf {
private:
    
    // Represent entire CNF formula as single array of integers
    // Consisting of sequence of fields:
    // 1. Number of variables
    // 2. Number of clauses
    // 3. For each clause, its starting index into the arx array
    // 4. A final index beyond the last class to make it easy to compute clause lengths
    // 5. Sequence of literals for each clause
    cnf_archive_t arx;

    // Cmap: Inverse mapping from projection variables to all clauses in which they occur
    // For each variable (both data and projection, give offset int cmap list
    // Offset for data variable = -1
    // Indexed by variable-1
    int *cmap_offsets;
    // Concatenated lists.  For each variable, start with number of clauses.  Then list their clause Ids
    int *cmap_lists;


public:
    Cnf();

    void import_file(FILE *infile);
    void import_archive(cnf_archive_t arx);

    // Destructor does not deallocate arx, since it might be passed on somewhere else
    ~Cnf();

    // Explicitly deallocate
    void deallocate();

    bool is_loaded() { return arx != NULL; }

    int variable_count();
    int clause_count();
    int clause_length(int id);
    // Index literals from 0
    int get_literal(int cid, int lid);
    // Both of these return true if successful
    bool show(FILE *outfile);
    bool write(FILE *outfile);
    
    // Run solver to determine whether satisfiable
    bool is_satisfiable();

    // Identify clauses with opposing literals
    void find_tautologies(std::unordered_set<int> &tauts);

    std::unordered_set<int> data_variables;
    std::unordered_map<int,q25_ptr> input_weights;

    // Accessing cmap entries
    int get_cmap_clause_count(int var);
    int get_cmap_cid(int var, int index);

private:
    void build_cmap();

};

// Previous state of literal to store on unit trail
struct utrail_ele {
    int lit;
    bool was_unit;
    bool was_bcp_unit;
};

// Add capabilities to CNF
class Clausal_reasoner {

 private:
    // Potential limit on BCP steps
    int bcp_step_limit;

    // Tracing variable
    int trace_variable;
    // Level in context management
    int context_level;
    

    // Current state of reasoner
    bool has_conflict;

    // All unit literals
    std::unordered_set<int> unit_literals;

    // Subset of unit literals derived by BCP.
    // Their unit clauses are considered part of the clausal state
    // Used as iterator
    std::unordered_set<int> bcp_unit_literals;

    // Variables that are currently being universally quantified
    // Their literals are considered unsatisfied
    std::unordered_set<int> quantified_variables;

    // Set of non-satisfied clauses in current context
    // Used as iterator
    std::set<int> active_clauses;
    // Allow further narrowing of the set of active clauses
    // This is only done when testing whether subset of clauses is locally satisfiable
    bool use_local_clauses;
    std::set<int> local_clauses;

    // Stacks to enable return to earlier state
    // Use value 0 to indicate start of new context
    
    // Unit literals
    std::vector<utrail_ele> unit_trail;
    // Quantified variables
    std::vector<int> uquant_trail;
    // Inactive clauses
    std::vector<int> clause_trail;

 public:

    // Underlying CNF
    Cnf *cnf;

    Clausal_reasoner(Cnf *icnf);

    ~Clausal_reasoner();

    // Set tracing variable
    void set_trace_variable(int var) { trace_variable = var; }

    void set_bcp_limit(int lim) { bcp_step_limit = lim; }

    // Begin new clausal context.
    void new_context();

    // Restore to previous context
    void pop_context();

    void assign_literal(int lit, bool bcp);



    void bcp(bool full);

    void quantify(int var);
    void partition(std::unordered_set<int> &vset);

    bool is_data_variable(int var) { return cnf->data_variables.find(var) != cnf->data_variables.end(); }

    // Extract a clausal representation of the current state
    cnf_archive_t extract();

    // Extract clausal representation and write as CNF file
    bool write(FILE *outfile);

    int current_clause_count();

    // Is the current state satisfiable?
    bool is_satisfiable();

    // Would the subset of clauses containing quantified variable be satisfiable?
    bool is_locally_satisfiable(int var);

    // Is the current state a conflict?
    bool is_conflict() { return has_conflict; }

    // Debugging support
    void show_units(FILE *outfile);

    // A hack to enable direct KC of simple formulas.
    // Applies only when KC can be expressed as product of clauses over distinct variables
    // If condition holds, fill up vector with zero-separated sequences of literals
    bool check_simple_kc(std::vector<int> &clause_chunks);
    

 private:

    // Can ignore this literal
    bool skip_literal(int lit) { 
	return unit_literals.find(-lit) != unit_literals.end() || 
	    quantified_variables.find(IABS(lit)) != quantified_variables.end(); }

    bool exit_clause(int lit) {
	return unit_literals.find(lit) != unit_literals.end();
    }

    bool skip_clause(int cid);

    int propagate_clause(int cid);
    // Return true if unpropagated unit literals remain
    bool unit_propagate();
    // Remove clause(s) from active clause set.  Don't do while iterating
    void deactivate_clause(int cid);
    void deactivate_clauses(std::vector<int> &remove);

    // Remove literal(s) from BCP literal set.  Don't do while iterating
    void deactivate_bcp_unit_literal(int lit);
    void deactivate_bcp_unit_literals(std::vector<int> &remove);

    // Detect conflict.  Clear entire clausal state
    void trigger_conflict();

    // Expand set of variables to include those that co-occur in clauses with given variables
    void expand_partition(std::unordered_set<int> &vset);

};
