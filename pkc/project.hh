#pragma once

#include "pog.hh"

class Project {
private:
    Clausal_reasoner *cr;
    Pog *pog;
    int root_literal;
    std::unordered_map<int,int> result_cache;

    // Optimization levels:
    // 0 : None
    // 1 : Do simple KC directly
    // 2 : Attempt to reuse previous results
    // 3 : Detect data-only and projection-only variables in CNF
    // 4 : Perform pure literal optimization
    int optlevel;

    // Debugging support
    int trace_variable;

    // Should mutex check be done just with local clauses
    bool use_local_satisfiability;

public:
    Project(const char *cnf_name, int opt);
    ~Project();
    void projecting_compile();
    bool write(const char *pog_name);

    // Perform weighted or unweighted model counting
    // Return NULL if weighted but no weights declared
    q25_ptr count(bool weighted);

    // Debugging support
    void show(FILE *outfile) { pog->show(root_literal, outfile); }

    void set_trace_variable(int var) { trace_variable = var; cr->set_trace_variable(var); }

    // Set whether to use local satisfiability
    void set_local_satisfiability(bool yes) { use_local_satisfiability = yes; }

    // Set BCP limit
    void set_bcp_limit(int lim) { if (cr) cr->set_bcp_limit(lim); }

private:
    // Perform ordinary knowledge compilation by invoking D4
    // Return edge representing root
    int compile(bool normal_form);
    // Traversal
    int traverse_sum(int edge);
    int traverse_product(int edge);
    int traverse(int edge);
};
