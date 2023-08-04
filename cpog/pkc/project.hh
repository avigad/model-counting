#pragma once

#include "pog.hh"

class Project {
private:
    Clausal_reasoner *cr;
    Pog *pog;
    int root_literal;

public:
    Project(const char *cnf_name);
    ~Project();


    int projecting_compile();

private:
    // Perform ordinary knowledge compilation by invoking D4
    // Return edge representing root
    int compile();
    // Traversal
    int traverse_sum(int edge);
    int traverse_product(int edge);
    int traverse(int edge);
};
