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
    bool canonized;
    // When clause created to serve as argument to lemma, it will
    // have an associated literal that will enable (set literal true) / disable (set literal false) the clause
    // Regular input clauses have activating literal = 0
    int activating_literal;

public:

    Clause();

    Clause(int *array, size_t len);

    Clause(FILE *infile, bool from_proof, bool *eof);

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

    void set_activating_literal(int alit);

    int get_activating_literal();

    // Simplify a clause according to a set of assigned literals
    // Return NULL if clause becomes satisfied
    // Return original if clause unchanged
    // Otherwise, return new clause
    Clause * simplify(std::unordered_set<int> &unit_literals);    

    // Compute a hash signature for the clause
    unsigned hash();

    // Compare with other clause for equality
    bool is_equal(Clause *op);

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

    // Temporary files that have been created during proof generation
    std::vector<const char *> file_names;
    
    // Map from local clause Id back to originating clause Id
    std::unordered_map<int,int> inverse_cid;

    // When empty clause gets added to CNF
    bool unsatisfiable;

    std::vector<Clause *> proof_clauses;
    int emitted_proof_clauses;

    std::vector<Clause *> proof_hints;

public:

    Cnf_reduced();
    
    ~Cnf_reduced();

    const char* get_file_name();

    // Delete intermediate files
    bool delete_files;

    // Add clause.  It will be simplified according to the context
    void add_clause(Clause *np, std::unordered_set<int> &unit_literals, int cid);
    
    // Run SAT solver.
    // Save away generated proof clauses
    // Return true if successful
    bool run_solver();

    // Helper functions

    // Read proof clauses + hints in LRAT format.
    // Ignore deletions
    // Return true if successful
    bool load_hinted_proof(FILE *infile);

    // Run SAT solver + checker
    // Save away generated proof clauses + hints
    // Return true if successful
    bool run_hinting_solver();

    // Retrieve next clause in proof.
    // Remap hint clause Ids to ones that match those in the larger proof
    // 
    // Be sure to retrieve the hint before the proof clause
    // start_id should be Id for first clause in proof sequence
    Clause *get_proof_hint(int start_id);

    // Retrieve next clause in proof.  Convert it to one usable by parent solver
    Clause *get_proof_clause(std::vector<int> *prefix);


};
 
// Augment clauses with reasoning and proof-generation capabilities 
class Cnf_reasoner : public Cnf {
private:

    // Counter to enable adding more extension variables
    int xvar_count;

    // Augmentation for POG clauses
    // Keep record of all active proof clauses
    std::vector<Clause *>proof_clauses;

    // Additional clauses used to construct proofs of lemmas
    // Each carries an activating literal indicating how to enable that clause within the formula
    // The clause numbers are sparse, and so store as map indexed by clause ID

    // Sparse representation of clauses, map from clause ID to clause
    std::unordered_map<int, Clause*> aux_clauses;

    // Mapping from hash of clause to its clause ID
    // Use vector, to deal with hash collisions
    std::unordered_map<unsigned,std::vector<int>*> aux_clause_lookup;

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

    // Read input clauses DIMACS format CNF file
    Cnf_reasoner(FILE *infile);

    // Has empty clause been added to proof?
    bool is_unsatisfiable();

    // Solver options.  Default for these are true.
    // Use drat-trim to supply hints for proof clauses generated by SAT solver
    bool use_drat;
    // Combine justification of multiple literals within conjunction into single proof
    bool multi_literal;
    // Use lemmas to represent shared nodes
    bool use_lemmas;
    // Delete intermediate files
    bool delete_files;
    // Limit on number of clauses before aborting
    int clause_limit;

    // Access input, proof, or auxilliary clause, with id 1 being first input clause
    Clause * get_clause(int cid);
    Clause * operator[](int);

    // POG generation.  Returns false if BCP shows formula is UNSAT
    bool enable_pog(Pog_writer *cw);

    void reset_xvar();
    int new_xvar();

    // Add clause as assertion.  Returns clause ID.  If unit clause, then add to set of unit clauses
    int start_assertion(Clause *clp);
    void add_hint(int hid);
    void add_hints(Clause *hp);
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
    void push_clause(int cid, bool force);
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

    // Possible modes for attempting literal validation
    typedef enum { 
	MODE_FULL, // Do everything
	MODE_BCP,  // Use BCP and then stop
	MODE_SAT   // Skip BCP and use SAT solver
    } validation_mode_t;


    // Justify that literal holds.  Return ID of justifying clause
    // If full, call SAT solver if necessary
    int validate_literal(int lit, validation_mode_t mode);

    // Justify that set of literals hold.
    // Justifying clauses IDs are then loaded into jids vector
    void validate_literals(std::vector<int> &lits, std::vector<int> &jids);

    // Delete all but final asserted clause
    void delete_assertions();

private:

    // Private methods for proof generation

    // Run SAT solver on reduced set of clauses as part of effort to validate literal lit.
    // Incorporate generated conflict proof into larger proof
    // Identify literals that will become unit and their justifying IDs
    int reduce_run(int lit);

    // Include/Exclude clause in BCP
    void activate_clause(int clit);
    void deactivate_clause(int clit);

    int add_proof_clause(Clause *clp);
    // Private methods for search support
    int found_conflict(int cid);
    void new_unit(int lit, int cid, bool input);

    // Validate unit when it can be done with just two hints
    int quick_validate_literal(int lit, int cid1, int cid2);

    // Handling of lemma argument clauses

    // Retrieve based on clause ID
    // Return NULL if not found
    Clause *get_aux_clause(int cid);

    // Find existing clause or create new one.  Return clause ID
    int find_or_make_aux_clause(Clause *np);

};


