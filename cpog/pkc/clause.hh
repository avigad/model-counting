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

// Manage temporary files
class File_manager {
private:
    // Names of files generated
    int buflen;
    char *buf;
    std::vector<const char *> names;
    const char *root;
    int sequence_number;
public:
    File_manager();
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


};

// Add capabilities to CNF
class Clausal_reasoner {

 private:
    // Underlying CNF
    Cnf *cnf;
    // Current state of reasoner
    std::unordered_set<int> unit_literals;
    std::unordered_set<int> quantified_variables;
    // Sets of non-satisfied clauses in current context
    // Must maintain two sets: current and active.  Swap these on each pass of BCP
    std::set<int> *curr_active_clauses;
    std::set<int> *next_active_clauses;

    // Stacks to enable return to earlier state
    // Use value 0 to indicate start of new context
    std::vector<int> unit_trail;
    std::vector<int> uquant_trail;
    std::vector<int> deactivated_clauses;

    // List of unit literals generated during BCP
    std::vector<int> bcp_units;

 public:

    Clausal_reasoner(Cnf *icnf);

    ~Clausal_reasoner();

    void new_context();
    void pop_context();

    void assign_literal(int lit);
    // Return true if encounter conflict
    bool bcp(int step_limit);

    void quantify(int var);
    void partition(std::unordered_set<int> &vset);

    // Extract a clausal representation of the current state
    cnf_archive_t extract();
    // Extract clausal representation and write as CNF file
    bool write(FILE *outfile);

    // Is the current state satisfiable?
    bool is_satisfiable();

 private:

    int propagate_clause(int cid);
    // Return true if unpropagated unit literals remain
    bool unit_propagate();
    void deactivate_clause(int cid);
    bool has_conflict();

};
