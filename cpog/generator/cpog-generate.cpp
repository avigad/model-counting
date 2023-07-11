// Translate DNNF representation into POG

// Usage: d2p [VLEVEL] file.cnf file.d4nnf

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "report.h"
#include "clausal.hh"
#include "pog.hh"
#include "writer.hh"
#include "counters.h"

static bool multi_literal = true;
static bool use_lemmas = true;
static bool delete_files  =  true;
static bool early_quit = false;
static bool one_sided = false;
static int drat_threshold = 20;
static int monolithic_threshold = 100000;
static float lemma_ratio = 5.0;
static int bcp_limit = 1;
static int clause_limit = INT_MAX;


void usage(const char *name) {
    lprintf("Usage: %s [-h] [-v VLEVEL] [-L LOG] [-p] [-1] [-m MONO] [-r RAT] [-C CLIM] [-b BLIM] [-t] [-s] [-e] [-k] FORMULA.cnf GRAPH.nnf [POG.cpog]\n", name);
    lprintf("  -h        Print this information\n");
    lprintf("  -v VLEVEL Set verbosity level\n");
    lprintf("  -L LOG    Record all results to file LOG\n");
    lprintf("  -p        Quit after determining POG size\n");
    lprintf("  -1        Generate a one-sided proof (only input clause deletions justified)\n");
    lprintf("  -m MONO   Monolithically validate subgraphs with tree size <= MONO\n");
    lprintf("  -r RAT    Scale factor for tree size threshold when lemma\n");
    lprintf("  -C CLIM   Limit total number of clauses in input + proof (default = %d)\n", clause_limit);
    lprintf("  -b BLIM   Limit depth of Boolean constraint propagation for contradiction proofs (default = %d)\n", bcp_limit);
    lprintf("  -t THRESH Use drat-trim on proofs when SAT problems are above THRESH clauses (default = %d)\n", drat_threshold);
    lprintf("  -s        Prove each literal separately, rather than combining into single proof\n");
    lprintf("  -e        Expand each node, rather than using lemmas\n");
    lprintf("  -k        Keep intermediate solver files\n");
    lprintf("FORMULA.cnf CNF representation of formula\n");
    lprintf("GRAPH.d4nnf Representation generated by D4\n");
    lprintf("POG.cpog    Output file\n");
    exit(0);
}

const char *prefix = "c GEN:";

static void stat_report() {
    if (verblevel < 1)
	return;
    double elapsed = get_elapsed();
    lprintf("%s Formula\n", prefix);
    lprintf("%s    input variables: %d\n", prefix, get_count(COUNT_VAR));
    lprintf("%s    input clauses  : %d\n", prefix, get_count(COUNT_CLAUSE));
    int nprod = get_count(COUNT_POG_AND);
    int nsum = get_count(COUNT_POG_OR);
    lprintf("%s POG nodes\n", prefix);    
    lprintf("%s    product   : %d\n", prefix, nprod);
    lprintf("%s    sum       : %d\n", prefix, nsum);
    lprintf("%s    node TOTAL: %d\n", prefix, nsum+nprod);
    lprintf("%s Other nodes\n", prefix);    
    lprintf("%s    aux product: %d\n", prefix, get_count(COUNT_AUX_AND));
    lprintf("%s Node visits\n", prefix);
    int vprod = get_count(COUNT_VISIT_AND);
    int vps = get_count(COUNT_VISIT_AND_SAT);
    int vpb = vprod-vps;
    int vsum = get_count(COUNT_VISIT_OR);
    lprintf("%s    product/BCP: %d\n", prefix, vpb);
    lprintf("%s    product/SAT: %d\n", prefix, vps);
    lprintf("%s    sum        : %d\n", prefix, vsum);
    lprintf("%s    visit TOTAL: %d\n", prefix, vsum+vprod);
    lprintf("%s Lemmas\n", prefix);
    lprintf("%s    definitions : %d\n", prefix, get_count(COUNT_LEMMA_DEFINITION));
    lprintf("%s    applications: %d\n", prefix, get_count(COUNT_LEMMA_APPLICATION));
    lprintf("%s    duplicates  : %d\n", prefix, get_count(COUNT_LEMMA_DUPLICATES));
    lprintf("%s    merged args : %d\n", prefix, get_count(COUNT_LEMMA_ARGUMENT_MERGE));
    ilist problem_histo = get_histo(HISTO_PROBLEM);
    int problem_count = 0;
    int problem_clauses = 0;
    int problem_min = 0;
    int problem_max = 0;
    for (int len = 0; len < ilist_length(problem_histo); len++) {
	if (problem_histo[len] > 0) {
	    if (problem_min == 0)
		problem_min = len;
	    problem_max = len;
	    problem_count += problem_histo[len];
	    problem_clauses += len * problem_histo[len];
	}
    }
    lprintf("%s SAT Problem Clause Counts (%d instances)\n", prefix, problem_count);
    if (verblevel >= 2) {
	for (int len = 0; len < ilist_length(problem_histo); len++) {
	    if (problem_histo[len] > 0) {
		lprintf("%s    %d : %d\n", prefix, len, problem_histo[len]);
	    }
	}
    }
    if (problem_count > 0) {
	lprintf("%s    PROBLEM TOTAL : %d\n", prefix, problem_clauses);
	lprintf("%s    PROBLEM MIN   : %d\n", prefix, problem_min);
	lprintf("%s    PROBLEM AVG   : %.2f\n", prefix, (double) problem_clauses/problem_count);
	lprintf("%s    PROBLEM MAX   : %d\n", prefix, problem_max);
    }

    if (problem_count > 0) {
	ilist proof_histo = get_histo(HISTO_PROOF);
	int proof_count = 0;
	int proof_clauses = 0;
	int proof_min = 0;
	int proof_max = 0;

	lprintf("%s SAT Proof Clause Counts\n", prefix);
	for (int len = 0; len < ilist_length(proof_histo); len++) {
	    if (proof_histo[len] > 0) {
		if (proof_min == 0)
		    proof_min = len;
		proof_max = len;
		proof_count += proof_histo[len];
		proof_clauses += len * proof_histo[len];
		if (verblevel >= 2)
		    lprintf("%s    %d : %d\n", prefix, len, proof_histo[len]);
	    }
	}
	if (proof_count > 0) {
	    lprintf("%s    PROOF TOTAL : %d\n", prefix, proof_clauses);
	    lprintf("%s    PROOF MIN   : %d\n", prefix, proof_min);
	    lprintf("%s    PROOF AVG   : %.2f\n", prefix, (double) proof_clauses/proof_count);
	    lprintf("%s    PROOF MAX   : %d\n", prefix, proof_max);
	}
    }

    int cd  = get_count(COUNT_DEFINING_CLAUSE);
    int cda = get_count(COUNT_DEFINING_AUX_CLAUSE);
    int cdp = cd-cda;
    int caj = get_count(COUNT_AND_JUSTIFICATION_CLAUSE);
    int coj = get_count(COUNT_OR_JUSTIFICATION_CLAUSE);
    int clj = get_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    int cla = get_count(COUNT_LEMMA_APPLICATION_CLAUSE);
    int clm = get_count(COUNT_MONOLITHIC_CLAUSE);
    lprintf("%s Clauses\n", prefix);    
    lprintf("%s    POG definition       : %d\n", prefix, cdp);
    lprintf("%s    AUX definition       : %d\n", prefix, cda);
    lprintf("%s    product justification: %d\n", prefix, caj);
    lprintf("%s    sum justification    : %d\n", prefix, coj);
    lprintf("%s    literal justification: %d\n", prefix, clj);
    lprintf("%s    lemma application    : %d\n", prefix, cla);
    lprintf("%s    monolithic proof     : %d\n", prefix, clm);
    lprintf("%s    clause TOTAL         : %d\n", prefix, cdp+cda+coj+caj+clj+cla+clm);
    double setup_time = get_timer(TIME_SETUP);
    double sat_time = get_timer(TIME_SAT);
    double delete_time = get_timer(TIME_DELETE);
    lprintf("%s Time\n", prefix);
    lprintf("%s   Setup POG           : %.2f\n", prefix, setup_time);
    lprintf("%s   Forward implication : %.2f\n", prefix, elapsed-(setup_time+delete_time));
    lprintf("%s             SAT execution  : %.2f\n", prefix, sat_time);
    lprintf("%s             Other forward  : %.2f\n", prefix, elapsed-(setup_time+delete_time+sat_time)); 
    lprintf("%s   Reverse implication : %.2f\n", prefix, delete_time);
    lprintf("%s   Time TOTAL          : %.2f\n", prefix, elapsed);
}

void panic() {
    err(false, "Execution incomplete.  Here's the results so far:\n");
    stat_report();
    err(false, "Results not valid\n");
}


// Return value is return code for program
static int run(FILE *cnf_file, FILE *nnf_file, Pog_writer *pwriter) {
    start_timer();
    Cnf_reasoner cnf(cnf_file);
    double elapsed = get_elapsed();
    lprintf("%s Time %.2f  Read input file with %d variables and %d clauses\n", prefix, elapsed, cnf.max_variable(), (int) cnf.clause_count());
    fclose(cnf_file);
    if (cnf.failed()) {
	fprintf(stderr, "Aborted\n");
	return 1;
    }
    cnf.multi_literal = multi_literal;
    cnf.use_lemmas = use_lemmas;
    cnf.delete_files = delete_files;
    cnf.drat_threshold = drat_threshold;
    cnf.clause_limit = clause_limit;
    cnf.bcp_limit = bcp_limit;
    cnf.monolithic_threshold = monolithic_threshold;
    cnf.lemma_ratio = lemma_ratio;
    Pog pog(&cnf);
    if (verblevel >= 2)
	pwriter->enable_comments();
    cnf.enable_pog(pwriter);
    if (!pog.read_d4ddnnf(nnf_file)) {
	err(false, "Error reading D4 NNF file\n");
	return 1;
    }
    elapsed = get_elapsed();
    lprintf("%s Time %.2f  Generated POG representation\n", prefix, elapsed);
    if (early_quit) {
	lprintf("%s POG created.  Exiting\n", prefix);
	return 0;
    }
    elapsed = get_elapsed();
    incr_timer(TIME_SETUP, elapsed);
    int root_literal = pog.get_root();
    report(3, "Justifying root literal %d\n", root_literal);
    int unit_cid = 0;
    if (one_sided)
	unit_cid = cnf.assert_literal(root_literal);
    else
	unit_cid = pog.justify(root_literal, false, use_lemmas);

    if (unit_cid == 0) {
	err(false, "Failed to justify root literal %d\n", root_literal);
	// Undercount
	return 10;
    }
    double start_deletion = get_elapsed();
    // For one-sided, may need to delete clauses added by initial BCP
    lprintf("%s Time %.2f  Completed forward implication proof\n", prefix, start_deletion);
    cnf.delete_assertions();
    elapsed = get_elapsed();
    lprintf("%s Time %.2f  Deleted asserted clauses\n", prefix, elapsed);
    bool ok = pog.delete_input_clauses(unit_cid);
    elapsed = get_elapsed();
    lprintf("%s Time %.2f  Deleted input clauses\n", prefix, elapsed);
    incr_timer(TIME_DELETE, elapsed-start_deletion);
    pwriter->finish_file();
    return ok ? 0 : 20;
}

int main(int argc, char *const argv[]) {
    FILE *cnf_file = NULL;
    FILE *nnf_file = NULL;
    Pog_writer *pwriter = NULL;
    verblevel = 1;
    int c;
    float r;
    set_panic(panic);
    while ((c = getopt(argc, argv, "hp1r:m:v:L:C:b:t:sek")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	    break;
	case 'p':
	    early_quit = true;
	    break;
	case '1':
	    one_sided = true;
	    break;
	case 'm':
	    monolithic_threshold = atoi(optarg);
	    break;
	case 'r':
	    r = atof(optarg);
	    lemma_ratio = r < 100 ? r : r/100.0;
	    break;
	case 'v':
	    verblevel = atoi(optarg);
	    break;
	case 'L':
	    set_logname(optarg);
	    break;
	case 'C':
	    clause_limit = atoi(optarg);
	    break;
	case 'b':
	    bcp_limit = atoi(optarg);
	    break;
	case 't':
	    drat_threshold = atoi(optarg);
	    break;
	case 's':
	    multi_literal = false;
	    break;
	case 'e':
	    use_lemmas = false;
	    break;
	case 'k':
	    delete_files = false;
	    break;
	case '?':
	default:
	    lprintf("Unknown option '%c'\n", c);
	    usage(argv[0]);
	}
    }
    int argi = optind;
    if (argi >= argc) {
	lprintf("Name of input CNF file required\n");
	usage(argv[0]);
    }
    cnf_file = fopen(argv[argi], "r");
    if (cnf_file == NULL) {
	lprintf("Can't open '%s'\n", argv[argi]);
	exit(1);
    }
    argi++;
    if (argi >= argc) {
	lprintf("Name of input NNF file required\n");
	usage(argv[0]);
    }
    nnf_file = fopen(argv[argi], "r");
    if (nnf_file == NULL) {
	fprintf(stderr, "Can't open '%s'\n", argv[argi]);
	exit(1);
    }
    argi++;
    if (argi < argc) {
	pwriter = new Pog_writer(argv[argi]);
	if (pwriter == NULL) {
	    fprintf(stderr, "Can't open '%s'\n", argv[argi]);
	    exit(1);
	}
	argi++;
    } else
	pwriter = new Pog_writer();

    if (!early_quit) {
	const char *sname;
	switch (SOLVER) {
	case KISSAT:
	    sname = "kissat";
	    break;
	case CADICAL:
	    sname = "cadical-drat";
	    break;
	case LCADICAL:
	    sname = "cadical-lrat";
	    break;
	case TCADICAL:
	    sname = "cadical-trimmed-lrat";
	    break;
	}

	lprintf("%s Program options\n", prefix);
	lprintf("%s   Multi-literal:       %s\n", prefix, multi_literal ? "yes" : "no");
	lprintf("%s   Use lemmas:          %s\n", prefix, use_lemmas ? "yes" : "no");
	lprintf("%s   Delete files:        %s\n", prefix, delete_files ? "yes" : "no");
	lprintf("%s   One-sided:           %s\n", prefix, one_sided ? "yes" : "no");
	lprintf("%s   DRAT threshold:      %d\n", prefix, drat_threshold);
	lprintf("%s   Clause limit:        %d\n", prefix, clause_limit);
	lprintf("%s   BCP limit:           %d\n", prefix, bcp_limit);
	lprintf("%s   Monolithic threshold %d\n", prefix, monolithic_threshold);
	lprintf("%s   Lemma ratio          %.2f\n", prefix, lemma_ratio);
	lprintf("%s   Solver:              %s\n", prefix, sname);
    }
    int return_code = 0;
    try {
	return_code = run(cnf_file, nnf_file, pwriter);
    } catch (const std::bad_alloc &e) {
	err(true, "Memory allocation error\n");
    }
    if (!early_quit)
	stat_report();
    
    return return_code;
}
