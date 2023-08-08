#pragma once

#include <cstdio>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include "clause.hh"

typedef enum { POG_NONE, POG_PRODUCT, POG_SUM, POG_NUM } pog_type_t;

// A POG edge is an integer, where the sign indicates whether it is
// positive or negated, and the magnitude indicates the edge destination.
// Edge destinations can be:
//  TAUTOLOGY
//  Variable: 1 <= var <= nvar
//  POG node values between nvar+1 and TAUTOLOGY-1

struct Node {
    int  offset;  // Offset into list of arguments
    pog_type_t type : 2;
    int degree  : 30;
};

class Pog {
private:
    // Number of input variables
    int nvar;
    // Concatenation of all operation arguments
    std::vector<int> arguments;
    // List of nodes, indexed by var-nvar-1
    std::vector<Node> nodes;
    // Unique table.  Maps from hash of operation + arguments to edge.
    std::unordered_multimap<unsigned, int> unique_table;
    

public:
    
    Pog(int n) { nvar = n; }
    ~Pog() {}

    bool get_phase(int edge) { return edge > 0; }
    int get_var(int edge) { return IABS(edge); }
    bool is_node(int edge) { int var = get_var(edge); return var > nvar && var != TAUTOLOGY; }
    int node_index(int edge) { int var = get_var(edge); return is_node(var) ? var-nvar-1 : -1; }
    int get_degree(int edge) { int idx = node_index(edge); return idx < 0 ? 0 : nodes[idx].degree; }
    pog_type_t get_type(int edge) { int idx = node_index(edge); return idx < 0 ? POG_NONE : nodes[idx].type; }

    int node_count() { return nodes.size(); }
    int edge_count() { return arguments.size(); }

    int *get_arguments(int edge) {
	int idx = node_index(edge); 
	return idx < 0 ? NULL : &arguments[nodes[idx].offset];
    }

    int get_argument(int edge, int index) { 
	int idx = node_index(edge); 
	return idx < 0 ? 0 : arguments[nodes[idx].offset + index];
    }

    int get_decision_variable(int edge);

    void get_variables(int root, std::unordered_set<int> &vset);

    // Creating a node
    void start_node(pog_type_t type);
    void add_argument(int edge);
    // Return edge for either newly created or existing node
    int finish_node();

    // Extract subgraph with designated root edge and write to file
    bool write(int root_edge, FILE *outfile);

    // Read NNF file and integrate into POG.  Return edge to new root
    int load_nnf(FILE *infile);

    // Check that only have data variables
    bool only_data_variables(int root, std::unordered_set<int> &data_variables);

    // Debugging 
    // If root = 0, dump entire POG.  Otherwise just those nodes reachable from root
    void show(int root, FILE *outfile);

    void show_edge(FILE *outfile, int edge);

private:

    // Collect Ids of all nodes reachable from root
    void visit(int edge, std::set<int> &visited);

    // Find subgraph with specified root.  Return mapping from old edges to new edges
    void get_subgraph(int root_edge, std::map<int,int> &node_remap);

    unsigned node_hash(int var);
    bool node_equal(int var1, int var2);


};
