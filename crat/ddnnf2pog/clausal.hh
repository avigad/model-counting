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

// Used to convert variable to literal of specified phase
#define MATCH_PHASE(v,p) ((p)<0?-(v):(v))

#include <vector>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <stdio.h>
#include <fstream>
#include "ilist.h"
#include "writer.hh"

// Representations of clauses and sets of clauses

// Clause is a vector of literals, each of which is a negative or positive integer.
// Tautologies are detected and represented as clause of the form -x, x
// When asserting contexts,
//   clauses are maintained so that the first two positions are unsatisfiable, if possible

class Clause {
private:
    ilist contents;
    bool is_tautology;
public:

    Clause();

    Clause(int *array, size_t len);

    Clause(FILE *infile, bool delete_ok, bool &eof);

    Clause (Clause *np);

    ~Clause();

    void add(int val);

    size_t length();

    bool tautology();

    int max_variable();

    void canonize();

    void show(char *fname);

    void show();

    void show(std::ofstream &outstream);

    void show(FILE *outfile);

    void write(Writer *writer);

    int *data();

    int& operator[](int);

    // Given array mapping (decremented) variable to 0/1
    // determine if clause satisfied
    bool satisfied(char *assignment);

    // Properties
    bool contains(int lit);

};

// Base class Cnf is a collection of clauses.  Can read from a DIMACS format CNF file
class Cnf {

private:
    
    int max_input_var;
    bool read_failed;

public:
    // Basic representation.
    // Should only be accessed by a superclass, but C++ doesn't provide this level of control
    std::vector<Clause *> clauses;

    Cnf();

    // Read clauses DIMACS format CNF file or DRAT file
    Cnf(FILE *infile);

    ~Cnf();

    // Did last read fail?
    bool failed();

    // Generate DIMACS CNF representation to stdout, outfile, or outstream
    void show();
    void show(FILE *outfile);
    void show(std::ofstream &outstream);
    void show(Cnf_writer *cwriter);

    // Return number of (input) clauses
    size_t clause_count();
    // Return ID of maximum (input) variable encountered
    int max_variable();

    // Given array mapping (decremented) variable to 0/1
    // determine if every clause satisfied.
    // If not, return ID of first offending clause.  Otherwise return 0
    int satisfied(char *assignment);

    Clause * get_input_clause(int cid);

    // Access input clause, with id 1 being first input clause
    Clause * operator[](int);    


    // Semi-private methods for general CNF
    // Add a new clause
    void add(Clause *clp);
};

// Special version of CNF that can store a reduced version of some larger CNF file
// where a set of unit literals simplifies clauses.
class Cnf_reduced : public Cnf {

    // So that can delete it when done
    const char *fname;
    // In some cases, will need to add new "nonstandard" variables that don't match 
    // ones in original input formula.  Want to track these so that can
    // map to and from variable numbers that get used by the SAT solver
    std::unordered_map<int,int> forward_variable_map;
    std::unordered_map<int,int> reverse_variable_map;

    // When empty clause gets added to CNF
    bool unsatisfiable;

    std::vector<Clause *> proof_clauses;
    int max_regular_variable;
    int max_nonstandard_variable;
    int emitted_proof_clauses;

public:
    

    Cnf_reduced();
    
    ~Cnf_reduced();

    const char* get_file_name();

    // Add nonstandard variable.  Should only do this after regular input clauses have been added
    void add_variable(int v);

    // Add clause.  It will be simplified according to the context
    // and the variables will get renamed by the forward map
    void add_clause(Clause *np, std::unordered_set<int> &unit_literals);
    
    // Run SAT solver.
    // Save away generated proof clauses
    // Return true if successful
    bool run_solver();

    // Retrieve next clause in proof.  Convert it to one usable by parent solver
    Clause *get_proof_clause(std::vector<int> *prefix);

};

// Augment clauses with reasoning and proof-generation capabilities 
class Cnf_reasoner : public Cnf {
private:

    // Augmentation for POG clauses
    std::vector<Clause *>proof_clauses;

    bool unsatisfiable;

    // Maintaining context 
    std::vector<int> context_literal_stack;
    std::vector<int> context_clause_stack;
    // Mapping from unit literal to asserting clause Id 
    std::unordered_map<int, int> justifying_ids;
    // Unit literals
    std::unordered_set<int> unit_literals;
    // List of assigned literals
    std::vector<int> assigned_literals;
   
    // Ordered sets of non-satisfied clauses in current context
    // Must maintain two sets: current and active.  Swap these on each pass of BCP
    std::set<int> *curr_active_clauses;
    std::set<int> *next_active_clauses;

    // Are hints being added to an assertion?
    bool asserting;
    // Stack of vectors containing deletion information
    // Each entry contains clause ID + hints
    std::vector<std::vector<int>*> deletion_stack;

public:

    // Direct access to writer (Use with caution)
    Pog_writer *pwriter;

    Cnf_reasoner();

    // Read input clauses DIMACS format CNF file
    Cnf_reasoner(FILE *infile);

    // Has empty clause been added to proof?
    bool is_unsatisfiable();

    // Access input or proof clause, with id 1 being first input clause
    Clause * get_clause(int cid);
    Clause * operator[](int);

    // POG generation.  Returns false if BCP shows formula is UNSAT
    bool enable_pog(Pog_writer *cw);

    // Add clause as assertion.  Returns clause ID.  If unit clause, then add to set of unit clauses
    int start_assertion(Clause *clp);
    void add_hint(int hid);
    void finish_command(bool add_zero);

    // Generate POG operation
    int start_and(int var, ilist args);
    int start_or(int var, ilist args);
    // Document operations
    void document_input(int cid);
    void document_and(int cid, int var, ilist args);
    void document_or(int cid, int var, ilist args);

    // Support for stack-based context saving
    void new_context();
    void pop_context();
    // Different things to put on the context stack:
    void push_assigned_literal(int lit);
    void push_derived_literal(int lit, int cid);
    void push_clause(int cid);
    std::vector<int> *get_assigned_literals();


    // set/get active clauses
    void extract_active_clauses(std::set<int> *save_set);
    void set_active_clauses(std::set<int> *new_set);

    // Partition set of active clauses into subsets having disjoint variables
    void partition_clauses(std::unordered_map<int,int> &var2rvar, std::unordered_map<int,std::set<int>*> &rvar2cset);

    // Extract a reduced representation of the currently active clauses
    Cnf_reduced *extract_cnf();

    // Perform Boolean constraint propagation.
    // Return ID of any generated conflict clause (or 0)
    int bcp();

    // Validate clause by RUP.  Add clause as assertion 
    // Return ID of validating clause (or 0 if fail)
    int rup_validate(Clause *cltp);

    // Justify that literal holds
    // Justify that literal holds.  Return ID of justifying clause
    int validate_literal(int lit);

    // Delete all but final asserted clause
    void delete_assertions();

private:

    // Private methods for proof generation
    int add_proof_clause(Clause *clp);
    // Private methods for search support
    int found_conflict(int cid);
    void new_unit(int lit, int cid, bool input);
};


