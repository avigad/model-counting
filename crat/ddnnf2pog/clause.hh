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
#include <map>
#include <stdio.h>
#include <fstream>
#include "ilist.h"

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

    Clause(FILE *infile);

    ~Clause();

    void add(int val);

    size_t length();

    bool tautology();

    int max_variable();

    void canonize();

    void show();

    void show(FILE *outfile);

    void show(std::ofstream &outstream);

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
    std::vector<Clause *> proof_clauses;
    int max_extension_var;

    // POG file
    FILE *pog_file;

    // Maintaining context 
    // Literals assigned during search
    std::vector<int> assigned_literals;
    // Literals derived by unit propagation
    std::vector<int> derived_literals;
    // Starting position of each layer of derived literals
    std::vector<int> literal_start_index;
    // Set representation of assigned and derived literals in current context
    std::unordered_set<int> unit_literals;
    // Mapping from unit literal to asserting clause Id 
    std::map<int, int> justifying_ids;
   
    // Ordered sets of non-satisfied clauses in current context
    // Must maintain two sets: current and active.  Swap these on each pass of BCP
    std::set<int> *curr_active_clauses;
    std::set<int> *next_active_clauses;
    // Stack of satisfied clauses
    std::vector<int> satisfied_ids;
    // Starting position of each layer of satisfied clauses
    std::vector<int> satisfied_start_index;

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
    int add_proof_clause(Clause *clp);

    // POG generation.  Returns false if BCP shows formula is UNSAT
    bool enable_pog(FILE *fp, int *cidp);

    // Search operation
    // Start new level of search by assigning literal and performing BCP
    // Return false if BCP finds conflict
    bool new_context(int lit);
    // Undo specified number of layers of search.
    // Perform BCP in event search detected conflict
    bool pop_context(int levels);



private:
    // Private methods for general CNF
    // Add a new clause
    void add(Clause *clp);

    // Private methods for search support
    int found_conflict(int cid);
    int new_unit(int lit, int cid, bool input);
    bool bcp();
};


