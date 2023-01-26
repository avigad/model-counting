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

void usage(const char *name) {
    printf("Usage: %s [-h] [-v VLEVEL] [-r] [-s] [-e] [-k] FORMULA.cnf GRAPH.d4nnf [POG.crat]\n", name);
    printf("  -h        Print this information\n");
    printf("  -v VLEVEL Set verbosity level\n");
    printf("  -r        Use own RUP proof generator, rather than drat-trim on SAT solver results\n");
    printf("  -s        Prove each literal separately, rather than combining into single proof\n");
    printf("  -e        Expand each node, rather than using lemmas\n");
    printf("  -k        Keep intermediate solver files\n");
    printf("FORMULA.cnf CNF representation of formula\n");
    printf("GRAPH.d4nnf Representation generated by D4\n");
    printf("POG.crat    Output file\n");
    exit(0);
}

bool use_drat = true;
bool multi_literal = true;
bool use_lemmas = true;
bool delete_files  =  true;

const char *prefix = "GEN";
static void report(double start) {
    double elapsed = tod()-start;
    printf("%s Formula\n", prefix);
    printf("%s    input variables: %d\n", prefix, get_count(COUNT_VAR));
    printf("%s    input clauses  : %d\n", prefix, get_count(COUNT_CLAUSE));
    int nprod = get_count(COUNT_POG_AND);
    int nsum = get_count(COUNT_POG_OR);
    printf("%s POG nodes\n", prefix);    
    printf("%s    product   : %d\n", prefix, nprod);
    printf("%s    sum       : %d\n", prefix, nsum);
    printf("%s    node TOTAL: %d\n", prefix, nsum+nprod);
    printf("%s Other nodes\n", prefix);    
    printf("%s    aux product: %d\n", prefix, get_count(COUNT_AUX_AND));
    printf("%s Node visits\n", prefix);
    int vprod = get_count(COUNT_VISIT_AND);
    int vps = get_count(COUNT_SAT_CALL);
    int vpb = vprod-vps;
    int vsum = get_count(COUNT_VISIT_OR);
    printf("%s    product/BCP: %d\n", prefix, vpb);
    printf("%s    product/SAT: %d\n", prefix, vps);
    printf("%s    sum        : %d\n", prefix, vsum);
    printf("%s    visit TOTAL: %d\n", prefix, vsum+vprod);
    printf("%s Lemmas\n", prefix);
    printf("%s    definitions : %d\n", prefix, get_count(COUNT_LEMMA_DEFINITION));
    printf("%s    applications: %d\n", prefix, get_count(COUNT_LEMMA_APPLICATION));
    int cd  = get_count(COUNT_DEFINING_CLAUSE);
    int cda = get_count(COUNT_DEFINING_AUX_CLAUSE);
    int cdp = cd-cda;
    int caj = get_count(COUNT_AND_JUSTIFICATION_CLAUSE);
    int coj = get_count(COUNT_OR_JUSTIFICATION_CLAUSE);
    int clj = get_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    printf("%s Clauses\n", prefix);    
    printf("%s    POG definition       : %d\n", prefix, cdp);
    printf("%s    AUX definition       : %d\n", prefix, cda);
    printf("%s    product justification: %d\n", prefix, caj);
    printf("%s    sum justification    : %d\n", prefix, coj);
    printf("%s    literal justification: %d\n", prefix, clj);
    printf("%s    clause TOTAL         : %d\n", prefix, cdp+cda+coj+caj+clj);
    double sat_time = get_timer(TIME_SAT);
    printf("%s Time\n", prefix);
    printf("%s   SAT execution  : %.2f\n", prefix, sat_time);
    printf("%s   other execution: %.2f\n", prefix, elapsed-sat_time);
    printf("%s   time TOTAL     : %.2f\n", prefix, elapsed);
}

static bool run(FILE *cnf_file, FILE *nnf_file, Pog_writer *pwriter) {
    Cnf_reasoner cnf(cnf_file);
    fclose(cnf_file);
    if (cnf.failed()) {
	fprintf(stderr, "Aborted\n");
	return false;
    }
    cnf.use_drat = use_drat;
    cnf.multi_literal = multi_literal;
    cnf.use_lemmas = use_lemmas;
    cnf.delete_files = delete_files;
    Pog pog(&cnf);
    if (verblevel >= 2)
	pwriter->enable_comments();
    cnf.enable_pog(pwriter);
    if (!pog.read_d4ddnnf(nnf_file)) {
	fprintf(stderr, "Error reading D4 NNF file\n");
	return false;
    }

    int root_literal = pog.get_root();
    report(3, "Justifying root literal %d\n", root_literal);

    int unit_cid = pog.justify(root_literal, false);
    cnf.delete_assertions();
    pwriter->comment("Delete input clauses");
    for (int cid = 1; cid <= cnf.clause_count(); cid++)
	pog.delete_input_clause(cid, unit_cid);
    pwriter->finish_file();
    return true;
}

int main(int argc, char *const argv[]) {
    FILE *cnf_file = NULL;
    FILE *nnf_file = NULL;
    Pog_writer *pwriter = NULL;
    verblevel = 1;
    double start = tod();
    int c;
    while ((c = getopt(argc, argv, "hv:rsek")) != -1) {
	switch (c) {
	case 'h':
	    usage(argv[0]);
	    break;
	case 'v':
	    verblevel = atoi(optarg);
	    break;
	case 'r':
	    use_drat = false;
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
	    printf("Unknown option '%c'\n", c);
	    usage(argv[0]);
	}
    }
    int argi = optind;
    if (argi >= argc) {
	printf("Name of input CNF file required\n");
	usage(argv[0]);
    }
    cnf_file = fopen(argv[argi], "r");
    if (cnf_file == NULL) {
	printf("Can't open '%s'\n", argv[argi]);
	exit(1);
    }
    argi++;
    if (argi >= argc) {
	printf("Name of input NNF file required\n");
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

    bool success = run(cnf_file, nnf_file, pwriter);
    report(start);
    
    return success ? 0 : 1;
}
