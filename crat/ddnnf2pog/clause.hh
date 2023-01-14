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

    Clause(FILE *infile, bool &eof);

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

};

// CNF is a collection of clauses.  Can read from a DIMACS format CNF file
class CNF {
private:
    // Basic representation
    std::vector<Clause *> clauses;
    int max_input_var;
    bool read_failed;

    // Augmentation for POG clauses
    std::vector<Clause *>proof_clauses;
    PogWriter *pwriter;

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

public:
    CNF();

    // Read clauses DIMACS format CNF file
    CNF(FILE *infile);

    // Did last read fail?
    bool failed();

    // Generate DIMACS CNF representation to stdout, outfile, or outstream
    void show();
    void show(FILE *outfile);
    void show(std::ofstream &outstream);
    void show(CnfWriter *cwriter);

    // Return number of (input) clauses
    size_t clause_count();
    // Return ID of maximum (input) variable encountered
    int max_variable();

    // Given array mapping (decremented) variable to 0/1
    // determine if every clause satisfied.
    // If not, return ID of first offending clause.  Otherwise return 0
    int satisfied(char *assignment);

    // Access input or proof clause, with id 1 being first input clause
    Clause * operator[](int);    

    // Proof related

    // POG generation.  Returns false if BCP shows formula is UNSAT
    bool enable_pog(PogWriter *cw);

    // Add clause as assertion.  Returns clause ID.  If unit clause, then add to set of unit clauses
    int start_assertion(Clause *clp);
    void add_hint(int hid);
    void finish_command(bool add_zero);

    // Generate POG operation
    int start_and(int var, ilist args);
    int start_or(int var, ilist args);
    // Document operations
    void document_and(int cid, int var, ilist args);
    void document_or(int cid, int var, ilist args);

    // Support for stack-based context saving
    void new_context();
    void pop_context();
    // Different things to put on the context stack:
    void push_assigned_literal(int lit);
    void push_derived_literal(int lit, int cid);
    void push_clause(int cid);

    // Perform Boolean constraint propagation.  Return false if hit conflict
    bool bcp();
    

    // Validate clause by RUP.  Add clause as assertion 
    // Return false if fail
    bool rup_validate(Clause *cltp);

private:
    // Private methods for general CNF
    // Add a new clause
    void add(Clause *clp);

    // Private methods for proof generation
    int add_proof_clause(Clause *clp);
    // Private methods for search support
    void found_conflict(int cid);
    void new_unit(int lit, int cid, bool input);
};


