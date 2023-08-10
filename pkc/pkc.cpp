#include <cstdio>
#include <cstdlib>
#include <unistd.h>


#include "report.h"
#include "counters.h"
#include "project.hh"


void usage(const char *name) {
    lprintf("Usage: %s [-h] [-k] [-v VLEVEL] [-O OPT] [-b BLIM] FORMULA.cnf [FORMULA.pog]\n", name);
    lprintf("  -h          Print this information\n");
    lprintf("  -k          Keep intermdiate files\n");
    lprintf("  -v VERB     Set verbosity level\n");
    lprintf("  -O OPT      Select optimization level: 0 None, 1 +Simple KC, 2 +Reuse, 3 +Analyze vars, 4 +Pure literal\n");
    lprintf("  -b BLIM     Limit iterations of Boolean constraint propagation\n");
}

const char *prefix = "c PKC:";

q25_ptr ucount = NULL;
q25_ptr wcount = NULL;

static void stat_report(double elapsed) {
    if (verblevel < 1)
	return;
    lprintf("%s Input Formula\n", prefix);
    lprintf("%s    Variables              : %d\n", prefix, get_count(COUNT_INPUT_VAR));
    lprintf("%s    Data variables         : %d\n", prefix, get_count(COUNT_DATA_VAR));
    lprintf("%s    Clauses                : %d\n", prefix, get_count(COUNT_INPUT_CLAUSE));

    lprintf("%s Initial POG\n", prefix);
    int ps, pp, pe;
    lprintf("%s    Initial POG Sum        : %d\n", prefix, ps = get_count(COUNT_POG_INITIAL_SUM));
    lprintf("%s    Initial POG Product    : %d\n", prefix, pp = get_count(COUNT_POG_INITIAL_PRODUCT));
    lprintf("%s    Initial POG Nodes      : %d\n", prefix, ps+pp);
    lprintf("%s    Initial POG Edges      : %d\n", prefix, pe = get_count(COUNT_POG_INITIAL_EDGES));
    lprintf("%s    Initial POG Clauses    : %d\n", prefix, ps+pp+pe);

    lprintf("%s POG nodes generated\n", prefix);
    lprintf("%s    Total POG Sum          : %d\n", prefix, ps = get_count(COUNT_POG_SUM));
    lprintf("%s    Total POG Product      : %d\n", prefix, pp = get_count(COUNT_POG_PRODUCT));
    lprintf("%s    Total POG Nodes        : %d\n", prefix, ps+pp);
    lprintf("%s    Total POG Edges        : %d\n", prefix, pe = get_count(COUNT_POG_EDGES));
    lprintf("%s    Total POG Clauses      : %d\n", prefix, ps+pp+pe);

    lprintf("%s Final POG\n", prefix);
    lprintf("%s    Final POG Sum          : %d\n", prefix, ps = get_count(COUNT_POG_FINAL_SUM));
    lprintf("%s    Final POG Product      : %d\n", prefix, pp = get_count(COUNT_POG_FINAL_PRODUCT));
    lprintf("%s    Final POG Nodes        : %d\n", prefix, ps+pp);
    lprintf("%s    Final POG Edges        : %d\n", prefix, pe = get_count(COUNT_POG_FINAL_EDGES));
    lprintf("%s    Final POG Clauses      : %d\n", prefix, ps+pp+pe);

    
    ilist sat_histo = get_histo(HISTO_SAT_CLAUSES);
    int clause_total = 0;
    int clause_max = 0;
    int clause_min = 0;
    int sat_count = get_count(COUNT_SAT_CALL);
    for (int len = 0; len < ilist_length(sat_histo); len++) {
	if (sat_histo[len] > 0) {
	    if (clause_min == 0)
		clause_min = len;
	    clause_max = len;
	    clause_total += len * sat_histo[len];
	}
    }
    lprintf("%s SAT calls\n", prefix);
    lprintf("%s    SAT TOTAL              : %d\n", prefix, sat_count);
    if (sat_count > 0) {
	lprintf("%s    SAT Clause MIN         : %d\n", prefix, clause_min);
	lprintf("%s    SAT Clause AVG         : %.2f\n", prefix, (double) clause_total / sat_count);
	lprintf("%s    SAT Clause MAX         : %d\n", prefix, clause_max);
    }

    ilist kc_clause_histo = get_histo(HISTO_KC_CLAUSES);
    clause_total = 0;
    clause_max = 0;
    clause_min = 0;
    int kc_count = get_count(COUNT_KC_CALL);
    for (int len = 0; len < ilist_length(kc_clause_histo); len++) {
	if (kc_clause_histo[len] > 0) {
	    if (clause_min == 0)
		clause_min = len;
	    clause_max = len;
	    clause_total += len * kc_clause_histo[len];
	}
    }
    lprintf("%s KC calls\n", prefix);
    lprintf("%s    KC TOTAL               : %d\n", prefix, kc_count);
    if (kc_count > 0) {
	lprintf("%s    KC Clause MIN          : %d\n", prefix, clause_min);
	lprintf("%s    KC Clause AVG          : %.2f\n", prefix, (double) clause_total / kc_count);
	lprintf("%s    KC clause MAX          : %d\n", prefix, clause_max);
    }

    ilist kc_pog_histo = get_histo(HISTO_POG_NODES);
    int pog_total = 0;
    int pog_max = 0;
    int pog_min = 0;
    for (int len = 0; len < ilist_length(kc_pog_histo); len++) {
	if (kc_pog_histo[len] > 0) {
	    if (pog_min == 0)
		pog_min = len;
	    pog_max = len;
	    pog_total += len * kc_pog_histo[len];
	}
    }
    lprintf("%s KC added POG nodes\n", prefix);
    lprintf("%s    KC Total               : %d\n", prefix, kc_count);
    lprintf("%s    KC POG MIN             : %d\n", prefix, pog_min);
    lprintf("%s    KC POG AVG             : %.2f\n", prefix, (double) pog_total / kc_count);
    lprintf("%s    KC POG MAX             : %d\n", prefix, pog_max);

    lprintf("%s Node Traversal:\n", prefix);
    int vp, vd, vm, ve;
    lprintf("%s    Traverse Product       : %d\n", prefix, vp = get_count(COUNT_VISIT_PRODUCT));
    lprintf("%s    Traverse Data Sum      : %d\n", prefix, vd = get_count(COUNT_VISIT_DATA_SUM));
    lprintf("%s    Traverse Mutex Sum     : %d\n", prefix, vm = get_count(COUNT_VISIT_MUTEX_SUM));    
    lprintf("%s    Traverse Excluding Sum : %d\n", prefix, ve = get_count(COUNT_VISIT_EXCLUDING_SUM));    
    lprintf("%s    Traverse TOTAL         : %d\n", prefix, vp+vd+vm+ve);

    lprintf("%s PKC Optimizations:\n", prefix);
    lprintf("%s    Simple KC              : %d\n", prefix, get_count(COUNT_SIMPLE_KC));
    lprintf("%s    Only data variables    : %d\n", prefix, get_count(COUNT_PKC_DATA_ONLY));
    lprintf("%s    Only projection vars   : %d\n", prefix, get_count(COUNT_PKC_PROJECT_ONLY));
    lprintf("%s    Result reuse           : %d\n", prefix, get_count(COUNT_PKC_REUSE));

    double init_kc_time = get_timer(TIME_INITIAL_KC);
    double kc_time = get_timer(TIME_KC);
    double sat_time = get_timer(TIME_SAT);
    double ring_time = get_timer(TIME_RING_EVAL);
    lprintf("%s Time\n", prefix);
    lprintf("%s    Initial KC time        : %.2f\n", prefix, init_kc_time);
    lprintf("%s    Other KC time          : %.2f\n", prefix, kc_time-init_kc_time);
    lprintf("%s    SAT time               : %.2f\n", prefix, sat_time);
    lprintf("%s    Ring evaluation time   : %.2f\n", prefix, ring_time);
    lprintf("%s    Other time             : %.2f\n", prefix, elapsed-kc_time-sat_time-ring_time);
    lprintf("%s    Time TOTAL             : %.2f\n", prefix, elapsed);
}

static int run(const char *cnf_name, const char *pog_name, int optlevel) {
    Project proj(cnf_name, optlevel);
    if (verblevel >= 5) {
	printf("Initial POG:\n");
	proj.show(stdout);
    }
    proj.projecting_compile();
    if (verblevel >= 5) {
	printf("Projected POG:\n");
	proj.show(stdout);
    }
    proj.write(pog_name);
    ucount = proj.count(false);
    wcount = proj.count(true);
    return 0;
}

int main(int argc, char *const argv[]) {
    FILE *cnf_file = NULL;
    verblevel = 1;
    int optlevel = 4;
    int bcp_limit = 0;
    bool keep = false;
    int c;
    while ((c = getopt(argc, argv, "hkv:O:b:")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	    return 0;
	case 'v':
	    verblevel = atoi(optarg);
	    break;
	case 'k':
	    keep = true;
	    break;
	case 'O':
	    optlevel = atoi(optarg);
	    break;
	case 'b':
	    bcp_limit = atoi(optarg);
	default:
	    lprintf("Unknown comandline option '%c'\n", c);
	    usage(argv[0]);
	    break;
	}

    }
    int argi = optind;
    if (argi >= argc) {
	lprintf("Name of input CNF file required\n");
	usage(argv[0]);
	return 1;
    }
    const char *cnf_name = argv[argi++];

    const char *pog_name = NULL;
    if (argi < argc)
	pog_name = argv[argi++];

    if (argi < argc) {
	lprintf("Unknown argument '%s'", argv[argi]);
	usage(argv[0]);
	return 1;
    }

    lprintf("%s Program options\n", prefix);
    if (bcp_limit > 0)
	lprintf("%s   BCP limit:                %d\n", prefix, bcp_limit);
    else
	lprintf("%s   BCP limit:                Unlimited\n", prefix);
    lprintf("%s   Optimization level:       %d\n", prefix, optlevel);

    double start = tod();
    int result = run(cnf_name, pog_name, optlevel);
    stat_report(tod()-start);
    if (ucount != NULL) {
	lprintf("%s  Unweighted count:", prefix);
	q25_write(ucount, stdout);
	lprintf("\n");
	q25_free(ucount);
    }
    if (wcount != NULL) {
	lprintf("%s  Weighted count:", prefix);
	q25_write(wcount, stdout);
	lprintf("\n");
	q25_free(wcount);
    }
    if (!keep)
	fmgr.flush();
    return result;
}
