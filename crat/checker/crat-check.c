/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University

  Permission is hereby granted, free of
  charge, to any person obtaining a copy of this software and
  associated documentation files (the "Software"), to deal in the
  Software without restriction, including without limitation the
  rights to use, copy, modify, merge, publish, distribute, sublicense,
  and/or sell copies of the Software, and to permit persons to whom
  the Software is furnished to do so, subject to the following
  conditions:
  
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


#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <sys/time.h>
#include <limits.h>


#define ERROUT stdout

#define MIN_SIZE 10
#define MAX_GAP 10
#define GROW_RATIO 1.45


/* Options */
int verb_level = 3;

/* Allow RUP proofs that encounter conflict before final hint */
bool early_rup = true;

/* Information for error reporting */
char *current_file = "";
int line_count = 0;

void usage(char *name) {
    printf("Usage: %s [-h] [-v VERB] FILE.cnf [FILE.crat]\n", name);
    printf(" -h VERB      Print this message\n");
    printf(" -v           Set verbosity level\n");
    printf("    FILE.cnf  Input CNF file\n");
    printf("    FILE.crat Input CRAT file\n");
    exit(0);
}

/*============================================
  Utility functions
============================================*/

double tod() {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) == 0)
	return (double) tv.tv_sec + 1e-6 * tv.tv_usec;
    else
	return 0.0;
}


/*============================================
   Integer lists
============================================*/

/*
  Data type ilist is used to represent clauses and clause id lists.
  These are simply lists of integers, where the value at position -1
  indicates the list length and the value at position -2 indicates the
  maximum list length.  The value at position -2 is positive for
  statically-allocated ilists and negative for ones that can be
  dynamically resized.
*/
typedef int *ilist;
  
/* Macros */
/*
  Difference between ilist maximum length and number of allocated
  integers
 */
#define ILIST_OVHD 2

#define ILIST_BASE(ils) ((ils)-ILIST_OVHD)
#define ILIST_LENGTH(ils) ((ils)[-1])
#define IABS(x) ((x)<0?(-x):(x))
#define ILIST_MAXLENGTHFIELD(ils) ((ils)[-2])
#define ILIST_MAXLENGTH(ils) (IABS(ILIST_MAXLENGTHFIELD(ils)))



ilist ilist_error(char *msg) {
    fprintf(ERROUT, "ERROR: File %s, Line %d.  ilist error in function %s\n", current_file, line_count+1, msg);
    exit(1);
    return NULL;
}

/* Allocate a new ilist. */
ilist ilist_new(int max_length) {
    if (max_length == 0)
	max_length++;
    int *p = calloc(max_length + ILIST_OVHD, sizeof(int));
    if (p == NULL) {
	fprintf(ERROUT, "Failed to allocate ilist of length %d\n", max_length);
	return ilist_error("ilist_new");
    }
    ilist result = p+ILIST_OVHD;
    ILIST_LENGTH(result) = 0;
    ILIST_MAXLENGTHFIELD(result) = -max_length;
    return result;
}

/* Free allocated ilist.  Will only free ones allocated via ilist_new */
void ilist_free(ilist ils) {
    if (!ils)
	return;
    if (ILIST_MAXLENGTHFIELD(ils) < 0) {
	int *p = ILIST_BASE(ils);
	free(p);
    }
}

/* Return number of elements in ilist */
int ilist_length(ilist ils) {
    return ILIST_LENGTH(ils);
}

/*
  Change size of ilist.  Can be shorter or longer than current.
  When lengthening, new contents are undefined
*/
ilist ilist_resize(ilist ils, int nlength) {
    int list_max_length = ILIST_MAXLENGTHFIELD(ils);
    int true_max_length = IABS(list_max_length);
    if (nlength > true_max_length) {
	if (list_max_length < 0) {
	    int *p = ILIST_BASE(ils);
	    int old_tml = true_max_length;
	    /* Dynamically resize */
	    true_max_length = (int) (true_max_length * GROW_RATIO);
	    if (nlength > true_max_length)
		true_max_length = nlength;
	    p = realloc(p, (true_max_length + ILIST_OVHD) * sizeof(int));
	    if (p == NULL) {
		/* Need to throw error here */
		fprintf(ERROUT, "Failed to grow ilist allocation from %d to %d\n",
			old_tml, true_max_length);
		return ilist_error("resize (dynamic)");
	    }
	    ils = p+ILIST_OVHD;
	    ILIST_MAXLENGTHFIELD(ils) = -true_max_length;
	} else 
	    /* Need to throw an error here */
	    return ilist_error("resize (static)");
    }
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Add new value(s) to end of ilist.
  For dynamic ilists, the value of the pointer may change
*/
ilist ilist_push(ilist ils, int val) {
    int length = ILIST_LENGTH(ils);
    int nlength = length+1;
    ils = ilist_resize(ils, nlength);
    if (!ils) {
	/* Want to throw an exception here */
	return ilist_error("push");
    }
    ils[length] = val;
    ILIST_LENGTH(ils) = nlength;
    return ils;
}

/*
  Sort integers in ascending order
 */
int int_compare_ilist(const void *i1p, const void *i2p) {
    int i1 = *(int *) i1p;
    int i2 = *(int *) i2p;
    if (i1 < i2)
	return -1;
    if (i1 > i2)
	return 1;
    return 0;
}


/*
  Put elements of ilist into ascending order
 */
void ilist_sort(ilist ils) {
    qsort((void *) ils, ilist_length(ils), sizeof(int), int_compare_ilist);
}


/*
  Print elements of an ilist separated by sep
 */
int ilist_print(ilist ils, FILE *out, const char *sep) {
    int i;
    int rval = 0;
    const char *space = "";
    if (ils == NULL) {
	rval = fprintf(out, "NULL");
	return rval;
    }
    for (i = 0; i < ilist_length(ils); i++) {
	int pval = fprintf(out, "%s%d", space, ils[i]);
	if (pval < 0)
	    return pval;
	rval += pval;
	space = sep;
    }
    return rval;
}

/*
  Print elements of an ilist separated by sep.  Return number of characters written
 */
int ilist_format(ilist ils, char *out, const char *sep, int maxlen) {
    int i;
    const char *space = "";
    int len = 0;
    for (i = 0; i < ilist_length(ils); i++) {
	if (len >= maxlen)
	    break;
	int xlen = snprintf(out+len, maxlen-len, "%s%d", space, ils[i]);
	len += xlen;
	space = sep;
    }
    out[len] = '\0';
    return len;
}

/***************
Integer Sets.  Extend ilist by listing all members in ascending order
 ***************/
/*
  Test whether value is member of list
*/
bool ilist_is_member(ilist ils, int val) {
    int i;
    for (i = 0; i < ilist_length(ils); i++)
	if (val == ils[i])
	    return true;
    return false;
}

bool ilist_is_disjoint(ilist ils1, ilist ils2) {
    int i1 = 0;
    int i2 = 0;
    int n1 = ilist_length(ils1);
    int n2 = ilist_length(ils2);
    while (i1 < n1 && i2 < n2) {
	int v1 = ils1[i1];
	int v2 = ils2[i2];
	if (v1 == v2)
	    return false;
	if (v1 < v2) 
	    i1++;
	else
	    i2++;
    }
    return true;
}

ilist ilist_union(ilist ils1, ilist ils2) {
    int i1 = 0;
    int i2 = 0;
    int n1 = ilist_length(ils1);
    int n2 = ilist_length(ils2);
    ilist rls = ilist_new(n1 < n2 ? n2 : n1);
    while (i1 < n1 && i2 < n2) {
	int v1 = ils1[i1];
	int v2 = ils2[i2];
	if (v1 < v2) {
	    rls = ilist_push(rls, v1);
	    i1++;
	} else if (v2 < v1) {
	    rls = ilist_push(rls, v2);
	    i2++;
	} else {
	    rls = ilist_push(rls, v1);
	    i1++; i2++;
	}
    }
    while (i1 < n1) {
	int v1 = ils1[i1++];
	rls = ilist_push(rls, v1);
    }
    while (i2 < n2) {
	int v2 = ils2[i2++];
	rls = ilist_push(rls, v2);
    }
    return rls;
}

ilist ilist_singleton(int v) {
    ilist rls = ilist_new(1);
    rls = ilist_push(rls, v);
    return rls;
}


/*============================================
  Set of literals
============================================*/


/*
  Represent set of literals as array indexed by variable.
  Maintain counter "current_generation"
  Entry +lset_generation indicates positive literal
  Entry -lset_generation indicates negative literal
  Any entry with value < |lset_generation| indicates neither literal in set
 */

int lset_generation = 0;
int *lset_array = NULL;
size_t lset_asize = 0;

void lset_error(char *msg) {
    fprintf(ERROUT, "ERROR: File %s, Line %d.  lset error in function %s\n", current_file, line_count+1, msg);
    exit(1);
}


void lset_init(int var) {
    lset_asize = MIN_SIZE;
    if (var > lset_asize)
	lset_asize = var;
    lset_array = calloc(lset_asize, sizeof(int));
    if (lset_array == NULL) {
	fprintf(ERROUT, "Couldn't allocate initial literal array of size %zd\n", lset_asize);
	lset_error("lset_init");
    }
    lset_generation = 1;
}

void lset_clear() {
    lset_generation++;
    if (lset_generation < 0) {
	int var;
	for (var = 1; var <= lset_asize; var++) 
	    lset_array[var-1] = 0;
	lset_generation = 1;
    }
}

void lset_check_size(int var) {
    if (lset_asize == 0) {
	lset_init(var);
	return;
    }
    if (var <= lset_asize)
	return;
    size_t nasize = (size_t) (lset_asize * GROW_RATIO);
    if (nasize < var)
	nasize = var;
    lset_array = realloc(lset_array, nasize * sizeof(int));
    if (verb_level >= 3) {
	printf("Resizing lset array %zd --> %zd\n", lset_asize, nasize);
    }
    if (lset_array == NULL) {
	fprintf(ERROUT, "Couldn't grow literal array size to %zd\n", nasize);
	lset_error("lset_check_size");
    }
    int nvar;
    for (nvar = lset_asize+1; nvar <= nasize; nvar++)
	lset_array[nvar-1] = 0;
    lset_asize = nasize;
}

int lset_get_lit(int var) {
    if (var <= 0 || var > lset_asize)
	return 0;
    int g = lset_array[var-1];
    if (g == lset_generation)
	return var;
    if (g == -lset_generation)
	return -var;
    return 0;
}

void lset_add_lit(int lit) {
    int var = IABS(lit);
    lset_check_size(var);

    int olit = lset_get_lit(var);

    if (olit != 0 && olit != lit) {
	fprintf(ERROUT, "Attempt to add literal %d.  Already have %d\n", lit, olit);
	lset_error("add_lit");
    }
    int val = lit > 0 ? lset_generation : -lset_generation;
    lset_array[var-1] = val;
}

void lset_show(FILE *out) {
    int var;
    fprintf(out, "[");
    bool first = true;
    for (var = 1; var <= lset_asize; var++) {
	int lit = lset_get_lit(var);
	if (lit == 0)
	    continue;
	if (first)
	    fprintf(out, "%d", lit);
	else
	    fprintf(out, ", %d", lit);
	first = false;
    }
    fprintf(out, "]");
}

/*============================================
  Processing Input
============================================*/

typedef enum {TOK_INT, TOK_STRING, TOK_STAR, TOK_EOF, TOK_EOL, TOK_NONE, TOK_UNKNOWN} token_t;

char *token_name[7] = { "integer", "string", "star", "EOF", "EOL", "NONE", "UNKNOWN" };

#define TOKEN_MAX 100
char token_last[TOKEN_MAX];
int token_value = 0;
FILE *token_file = NULL;
int token_pos = 0;

void token_error(char *msg) {
    fprintf(ERROUT, "ERROR: File %s, Line %d.  token error in function %s\n", current_file, line_count+1, msg);
    exit(1);
}



void token_setup(char *fname) {
    token_file = fopen(fname, "r");
    current_file = strdup(fname);
    if (token_file == NULL) {
	fprintf(ERROUT, "Couldn't open file '%s'\n", fname);
	token_error("token_setup");
    }
    line_count = 0;
}

void token_finish() {
    fclose(token_file);
    token_file = NULL;
}


token_t token_next() {
    int sign = 1;
    int mag = 0;
    token_t ttype = TOK_NONE;
    token_pos = 0;
    token_last[token_pos] = '\0';
    token_value = 0;
    int c;
    bool done = false;
    while (!done) {
	c = fgetc(token_file);
	if (c == EOF) {
	    ttype = TOK_EOF;
	    done = true;
	} else  if (c == '\n') {
	    line_count ++;
	    ttype = TOK_EOL;
	    done = true;
	} else if (!isspace(c)) {
	    ungetc(c, token_file);
	    break;
	}
    }

    while (!done) {
	if (token_pos >= TOKEN_MAX-1) {
	    ttype = TOK_UNKNOWN;
	    done = true;
	}
	c = fgetc(token_file);
	if (c == '-') {
	    if (ttype != TOK_NONE) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		sign = -sign;
		ttype = TOK_INT;
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
	    }
	} else if (isdigit(c)) {
	    if (ttype != TOK_NONE && ttype != TOK_INT) {
		ttype =  TOK_UNKNOWN;
		done = true;
	    } else {
		ttype = TOK_INT;
		mag = 10 * mag + (c - '0');
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
		token_value = sign * mag;
	    }
	} else if (isspace(c)) {
	    if (c == '\n') {
		ungetc(c, token_file);
	    }
	    done = true;
	} else if (c == '*') {
	    if (ttype != TOK_NONE) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
		ttype = TOK_STAR;
	    }
	} else {
	    if (ttype != TOK_NONE && ttype != TOK_STRING) {
		ttype = TOK_UNKNOWN;
		done = true;
	    } else {
		ttype = TOK_STRING;
		token_last[token_pos++] = c;
		token_last[token_pos] = '\0';
	    }
	}
    }
    if (verb_level >= 4)
	printf("Read token.  Line = %d.  Token = '%s'.  Type = %s\n", line_count+1, token_last, token_name[ttype]);
    return ttype;
}

void token_confirm_eol() {
    /* Done */
    token_t token = token_next();
    if (token != TOK_EOL) {
	fprintf(ERROUT, "Expected end of line.  Got %s ('%s') instead\n", token_name[token], token_last);
	token_error("token_confirm_eol");
    }
}

void token_find_eol() {
    int c;
    while (true) {
	c = fgetc(token_file);
	if (c == EOF)
	    return;
	if (c == '\n') {
	    line_count ++;
	    return;
	}
    }
}

/*============================================
  Core data structures
============================================*/

/* Maintain set of all clauses as single array.  Each entry zero-terminated */
int *clause_list = NULL;
int clause_next_pos = 0;
int clause_asize = 0;
int clause_count = 0;
int clause_last_id = 0;

/*
  Assume that clauses come in consecutively numbered blocks, but with gaps between them
  Maintain as linked list of blocks
 */


typedef struct BELE {
    int start_id;  // Clause ID of initial entry
    int length;    // Number of (possibly null) clauses in block
    ilist offset;  // Sequence of clause offsets
    struct BELE *next; 
} clause_block_t;

clause_block_t *clause_set = NULL;
clause_block_t *clause_set_last = NULL;

void clause_error(char *msg) {
    fprintf(ERROUT, "ERROR: File %s, Line %d.  clause error in function %s\n", current_file, line_count+1, msg);
    exit(1);
}

/* Operations */
void clause_init() {
    clause_asize = MIN_SIZE;
    clause_list = calloc(clause_asize, sizeof(int));
    if (clause_list == NULL) {
	fprintf(ERROUT, "Couldn't allocate space for clauses\n");
	clause_error("clause_init");
    }
    clause_set = malloc(sizeof(clause_block_t));
    if (clause_set == NULL) {
	fprintf(ERROUT, "Couldn't allocate space for clause block\n");
	clause_error("clause_init");
    }
    clause_set->start_id = 1;
    clause_set->length = 0;
    clause_set->offset = ilist_new(100);
    clause_set->next = NULL;
    clause_set_last = clause_set;
}

/* Get start of clause */
int *clause_locate(int cid) {
    clause_block_t *block = clause_set;
    while (true) {
	if (block == NULL)
	    return NULL;
	int pos = cid - block->start_id;
	if (pos < 0)
	    return NULL;
	if (pos <  block->length) {
	    int offset = block->offset[pos];
	    if (offset < 0)
		return NULL;
	    return clause_list + offset;
	}
	block = block->next;
    }
}

bool clause_delete(int cid) {
    clause_block_t *block = clause_set;
    while (true) {
	if (block == NULL)
	    return false;
	int pos = cid - block->start_id;
	if (pos < 0)
	    return false;
	if (pos <  block->length) {
	    bool deleted = block->offset[pos] >= 0;
	    block->offset[pos] = -1;
	    return deleted;
	}
	block = block->next;
    }
}

void clause_new(int cid) {
    if (clause_last_id == 0)
	clause_init();
    if (clause_locate(cid) != NULL) {
	fprintf(ERROUT, "Can't add clause %d.  Clause Id already defined\n", cid);
	clause_error("clause_new");
    }
    if (cid > clause_last_id + MAX_GAP) {
	/* Need to start new block */
	clause_block_t *nlast = malloc(sizeof(clause_block_t));
	if (nlast == NULL) {
	    fprintf(ERROUT, "Couldn't allocate space for clause block\n");
	    clause_error("clause_new");
	}
	if (verb_level >= 3) {
	    printf("Starting new clause block.  Id = %d\n", cid);
	}
	nlast->start_id = cid;
	nlast->length = 0;
	nlast->offset = ilist_new(MIN_SIZE);
	nlast->next = NULL;
	clause_set_last->next = nlast;
	clause_set_last = nlast;
    } else {
	/* Fill in with null clauses */
	int ncid;
	for (ncid = clause_last_id+1; ncid < cid; ncid++) {
	    clause_set_last->offset = ilist_push(clause_set_last->offset, -1);
	    clause_set_last->length ++;
	}
    }
    clause_set_last->offset = ilist_push(clause_set_last->offset, clause_next_pos);
    clause_set_last->length ++;
    clause_last_id = cid;
    clause_count ++;
}

/* Add either literal or terminating 0 to current clause */
void clause_add_literal(int lit) { 
    if (clause_next_pos >= clause_asize) {
	int oasize = clause_asize;
	clause_asize = (int) (GROW_RATIO * clause_asize);
	clause_list = realloc(clause_list, clause_asize * sizeof(int));
	if (verb_level >= 3) {
	    printf("Resizing clause list %d --> %d\n", oasize, clause_asize);
	}
	if (clause_list == NULL) {
	    fprintf(ERROUT, "Couldn't allocate space for clauses\n");
	    clause_error("clause_add_literal");
	}
    }
    clause_list[clause_next_pos++] = lit;
}

/* Number of literals in clause (not counting terminating 0) */
int clause_length(int *lits) {
    int i;
    for (i = 0; lits[i] != 0; i++)
	;
    return i;
}

bool clause_is_unit(int *lits) {
    return lits != NULL 
	&& lits[0] != 0
	&& lits[1] == 0;
}

void clause_show(FILE *out, int cid, bool endline) {
    int *loc = clause_locate(cid);
    if (loc == NULL) {
	return;
    } 
    fprintf(out, "%d:", cid);
    while (*loc != 0) {
	fprintf(out, " %d", *loc);
	loc++;
    }
    if (endline)
	fprintf(out, "\n");
}

void clause_show_all(FILE *out) {
   clause_block_t *block = clause_set;
    while (block != NULL) {
	int i;
	for (i = 0; i < block->length; i++) {
	    clause_show(out, block->start_id + i, true);
	}
	block = block->next;
    }
}

/*============================================
  RUP
============================================*/

#define RUP_CONFLICT INT_MAX
#define RUP_STALL 0

void rup_error(char *msg) {
    fprintf(ERROUT, "ERROR: File %s, Line %d.  RUP error in function %s\n", current_file, line_count+1, msg);
    exit(1);
}


/* Initialize lset to complement of literals */
void rup_setup(int *lits) {
    lset_clear();
    int lit;
    while ((lit = *lits) != 0) {
	lset_add_lit(-lit);
	lits++;
    }
}

int rup_unit_prop(int cid) {
    int *lits = clause_locate(cid);
    if (lits == NULL) {
	fprintf(ERROUT, "Clause #%d deleted or never existed\n", cid);
	rup_error("rup_unit_prop");
    }
    int unit = RUP_CONFLICT;
    int lit;
    while ((lit = *lits) != 0) {
	lits++;
	int var = IABS(lit);
	int rlit = lset_get_lit(var);
	if (rlit == lit)
	    return RUP_STALL;
	else if (rlit == -lit)
	    continue;
	else if (unit == RUP_CONFLICT)
	    unit = lit;
	else
	    return RUP_STALL;
    }
    return unit;
}


/* Run RUP on hints from file.  Assume already set up  */
void rup_run() {
    bool conflict = false;
    int steps = 0;
    while (true) {
	token_t token = token_next();
	if (token != TOK_INT) {
	    fprintf(ERROUT, "Expecting integer hint.  Got %s ('%s') instead\n", token_name[token], token_last);
	    rup_error("rup_run");
	} else if (token_value == 0) {
	    if (!conflict) {
		fprintf(ERROUT, "RUP failure.  Didn't have conflict on final clause\n");
		rup_error("rup_run");
	    } else if (verb_level >= 3)
		printf("Line %d.  RUP succeeded in %d steps\n", line_count+1, steps);
	    return;
	} else {
	    if (conflict) {
		if (early_rup) {
		    while (token_value != 0) {
			token = token_next();
			if (token != TOK_INT) {
			    fprintf(ERROUT, "Expecting integer hint.  Got %s ('%s') instead\n", token_name[token], token_last);
			    rup_error("rup_run");
			}
		    }
		    if (verb_level >= 3)
			printf("Line %d.  RUP succeeded in %d steps\n", line_count+1, steps);
		    return;
		} else {
		    fprintf(ERROUT, "RUP failure.  Encountered conflict after processing %d hints.  Not at end of hints list\n", steps);
		    rup_error("rup_run");
		}
	    }
	    int cid = token_value;
	    int unit = rup_unit_prop(cid);
	    steps ++;
	    if (unit == RUP_CONFLICT)
		conflict = true;
	    else if (unit == RUP_STALL) {
		fprintf(ERROUT, "RUP failure.  Clause %d did not cause unit propagation\n", cid);
		if (verb_level >= 2) {
		    fprintf(ERROUT, "Added literals: ");
		    lset_show(ERROUT);
		    fprintf(ERROUT, "\n");
		    fprintf(ERROUT, "Clause ");
		    clause_show(ERROUT, cid, true);
		}
		rup_error("rup_run");
	    } else
		lset_add_lit(unit);
	}

    }
}


/*============================================
  Processing files
============================================*/

int input_clause_count = 0;
int input_variable_count = 0;

void cnf_read(char *fname) {
    token_setup(fname);
    /* Find and parse header */
    while (true) {
	token_t token = token_next();
	if (token != TOK_STRING) {
	    fprintf(ERROUT, "Unexpected token '%s' while looking for CNF header\n", token_last);
	    token_error("cnf_read");
	}
	if (token_last[0] == 'c')
	    token_find_eol();
	else if (token_last[0] == 'p') {
	    if (token_last[1] != '\0') {
		fprintf(ERROUT, "ERROR: Invalid CNF field '%s'\n", token_last);
		token_error("cnf_read");
	    }
	    token = token_next();
	    if (strcmp(token_last, "cnf") != 0) {
		fprintf(ERROUT, "ERROR: Expected field 'cnf'.  Got '%s'\n", token_last);
		token_error("cnf_read");
	    }
	    token = token_next();
	    if (token != TOK_INT) {
		fprintf(ERROUT, "ERROR: Invalid CNF variable count '%s'\n", token_last);
		token_error("cnf_read");
	    }
	    input_variable_count = token_value;
	    token = token_next();
	    if (token != TOK_INT) {
		fprintf(ERROUT, "ERROR: Invalid CNF clause count '%s'\n", token_last);
		token_error("cnf_read");
	    }
	    input_clause_count = token_value;
	    token = token_next();
	    if (token != TOK_EOL) {
		fprintf(ERROUT, "ERROR: Invalid field in CNF header '%s'\n", token_last);
		token_error("cnf_read");
	    }
	    break;
	} else {
	    fprintf(ERROUT, "Unexpected token '%s' while reading CNF header\n", token_last);
	    token_error("cnf_read");
	}
    }
    /* Read clauses */
    int found_clause_count = 0;
    bool within_clause = false;
    while (true) {
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	else if (token == TOK_STRING && token_last[0] == 'c')
	    token_find_eol();
	else if (token == TOK_EOL)
	    continue;
	else if (token == TOK_INT) {
	    if (!within_clause) {
		clause_new(found_clause_count+1);
		within_clause = true;
	    }
	    clause_add_literal(token_value);
	    if (token_value == 0) {
		found_clause_count ++;
		within_clause = false;
	    }
	}
	else {
	    fprintf(ERROUT, "Unexpected token '%s' found in CNF file\n", token_last);
	    token_error("cnf_read");
	}
    }
    if (found_clause_count != input_clause_count) {
	fprintf(ERROUT, "Invalid CNF.  Expected %d clauses.  Found %d\n", input_clause_count, found_clause_count);
	token_error("cnf_read");
    }
    token_finish();
    if (verb_level >= 1) {
	printf("CHECK: Read CNF file with %d variables and %d clauses\n", input_variable_count, input_clause_count);
    }
}

void cnf_show(FILE *out) {
    int cid;
    if (verb_level < 1)
	return;
    printf("CNF File.  %d clauses\n", input_clause_count);
    for (cid = 1; cid <= input_clause_count; cid++) {
	clause_show(out, cid, true);
    }
}

typedef enum {NODE_PRODUCT, NODE_SUM, NODE_NONE} node_type_t;

typedef struct {
    node_type_t type;
    int id;
    int cid;
    ilist dependency_list;
    ilist children;
} node_t;

node_t *node_list = NULL;
int node_asize = 0;
int node_count = 0;


void crat_error(char *msg) {
    fprintf(ERROUT, "ERROR: File %s, Line %d.  crat error in function %s\n", current_file, line_count+1, msg);
    exit(1);
}

node_t *node_find(int id) {
    int idx = id - input_variable_count - 1;
    if (idx < 0 || idx >= node_asize)
	return NULL;
    return &node_list[idx];
}

node_t *node_new(node_type_t type, int id, int cid) {
    if (id <= input_variable_count) {
	fprintf(stdout, "Invalid operation id %d\n", id);
	crat_error("node_new");
    }
    if (id-input_variable_count > node_asize) {
	int nasize = id-input_variable_count;
	if (nasize < MIN_SIZE)
	    nasize = MIN_SIZE;
	if (nasize < (int) (GROW_RATIO * node_asize))
	    nasize = (int) (GROW_RATIO * node_asize);
	if (node_list == NULL)
	    node_list = calloc(nasize, sizeof(node_t));
	else
	    node_list = realloc(node_list, nasize * sizeof(node_t));
	if (node_list == NULL) {
	    fprintf(ERROUT, "Couldn't allocate space for node list of size %d\n", nasize);
	    crat_error("node_new");
	}
	int idx;
	for (idx = node_asize; idx < nasize; idx++) {
	    int nid = idx + input_variable_count;
	    node_list[idx].type = NODE_NONE;
	    node_list[idx].id = nid;
	    node_list[idx].cid = 0;
	    node_list[idx].dependency_list = NULL;
	    node_list[idx].children = NULL;
	}
	if (verb_level >= 3) {
	    printf("Resized node array %d --> %d\n", node_asize, nasize);
	}
	node_asize = nasize;
    }
    node_t *node = node_find(id);
    if (node->type != NODE_NONE) {
	fprintf(ERROUT, "Cannot create new node with id %d.  Id already in use\n", id);
	crat_error("node_new");
    }
    node->type = type;
    node->cid = cid;
    node_count ++;
    return node;
}

int crat_operation_count = 0;
int crat_assertion_count = 0;
int crat_assertion_deletion_count = 0;
int crat_operation_clause_count = 0;

void crat_show(FILE *out) {
    int cid;
    int idx, nid;
    printf("CRAT Operations\n");
    for (idx = 0; idx < node_asize; idx++) {
	nid = input_variable_count + 1 + idx;
	node_t *node = node_find(nid);
	if (node == NULL || node->type == NODE_NONE)
	    continue;
	fprintf(out, "N%d: %s(", nid, node->type == NODE_PRODUCT ? "AND" : "OR");
	ilist_print(node->children, out, ", ");
	fprintf(out, ")\n");
	int n = ilist_length(node->children);
	int i;
	for (i = 0; i <= n; i++) {
	    fprintf(out, "  ");
	    clause_show(out, node->cid + i, true);
	}
    }
}

/* Handlers for different command types.  Each starts after parsing command token */
void crat_add_clause(int cid) {
    lset_clear();
    clause_new(cid);
    while (true) {
	token_t token = token_next();
	if (token != TOK_INT) {
	    fprintf(ERROUT, "Unexpected token '%s'\n", token_last);
	    crat_error("crat_add_clause");
	}

	int lit = token_value;
	clause_add_literal(lit);

	if (lit == 0)
	    break;
	else
	    lset_add_lit(-lit);
    }
    rup_run();

    token_confirm_eol();

    crat_assertion_count ++;

    if (verb_level >= 3) {
	printf("Line %d.  Processed clause %d addition\n", line_count, cid);
    }

}
void crat_delete_clause() {
    /* Before start deletions, lets show what was there */ 
    if (verb_level >= 3 && crat_assertion_deletion_count == 0) {
	printf("Before performing deletions\n");
	crat_show(stdout);
	printf("All clauses:\n");
	clause_show_all(stdout);
    }
    token_t token = token_next();
    if (token != TOK_INT) {
	fprintf(ERROUT, "Unexpected token '%s'\n", token_last);
	crat_error("crat_delete_clause");
    }
    int cid = token_value;
    int *lits = clause_locate(cid);
    rup_setup(lits);

    bool deleted = clause_delete(cid);
    if (!deleted) {
	fprintf(ERROUT, "Could not delete clause %d.  Never defined or already deleted\n", cid);
	crat_error("crat_delete_clause");
    }

    rup_run();

    token_find_eol();
    crat_assertion_deletion_count ++;

    if (verb_level >= 3) {
	printf("Line %d.  Processed clause %d deletion\n", line_count, cid);
    }
    

}

void crat_add_product(int cid) {
    token_t token = token_next();
    if (token != TOK_INT) {
	fprintf(ERROUT, "Expected operation number.  Got %s ('%s') instead\n", token_name[token], token_last);
	crat_error("crat_add_product");
    } 
    int nid = token_value;
    node_t *node = node_new(NODE_PRODUCT, nid, cid);
    node->children = ilist_new(2);
    node->dependency_list = ilist_new(1);
    ilist local_dependency_list = ilist_new(0);

    /* Get children */
    while (true) {
	token = token_next();
	if (token != TOK_INT) {
	    fprintf(ERROUT, "Expected product operation argument.  Got %s ('%s') instead\n", token_name[token], token_last);
	    crat_error("crat_add_product");
	}
	if (token_value == 0)
	    break;
	int lit = token_value;
	int var = IABS(lit);
	node->children = ilist_push(node->children, lit);
	if (var <= input_variable_count) {
	    if (ilist_is_member(node->dependency_list, var) || ilist_is_member(local_dependency_list, var)) {
		fprintf(ERROUT, "Can't add literal %d to node %d children.  Variable %d already in dependency set\n", lit, nid, var);
		crat_error("add_product");
	    }
	    local_dependency_list = ilist_push(local_dependency_list, var);
	} else {
	    node_t *cnode = node_find(var);
	    if (cnode == NULL || cnode->type == NODE_NONE) {
		fprintf(ERROUT, "Can't add literal %d to node %d children.  Invalid node Id %d\n", lit, nid, var);
		crat_error("add_product");
	    }
	    if (!ilist_is_disjoint(node->dependency_list, cnode->dependency_list) ||
		!ilist_is_disjoint(local_dependency_list, cnode->dependency_list)) {
		fprintf(ERROUT, "Can't add literal %d to node %d children.  Overlapping dependency sets\n", lit, nid);
		crat_error("add_product");
	    }
	    ilist save = node->dependency_list;
	    node->dependency_list = ilist_union(node->dependency_list, cnode->dependency_list);
	    ilist_free(save);
	}
    }
    if (ilist_length(local_dependency_list) > 0) {
	ilist_sort(local_dependency_list);
	ilist save = node->dependency_list;
	node->dependency_list = ilist_union(node->dependency_list, local_dependency_list);
	ilist_free(save);
    }
    ilist_free(local_dependency_list);
    if (ilist_length(node->children) < 2) {
	fprintf(ERROUT, "Sum node %d has %d childen.  Must have >= 2\n", nid, ilist_length(node->children));
	crat_error("crat_add_conjunction");
    }

    /* Done */
    token = token_next();
    if (token != TOK_EOL) {
	fprintf(ERROUT, "Expected end of line.  Got %s ('%s') instead\n", token_name[token], token_last);
	crat_error("crat_add_product");
    }

    /* Add clauses */
    clause_new(cid);
    clause_add_literal(nid);
    int i;
    int n = ilist_length(node->children);
    for (i = 0; i < n; i++)
	clause_add_literal(-node->children[i]);
    clause_add_literal(0);
    for (i = 0; i < n; i++) {
	clause_new(cid+i+1);
	clause_add_literal(-nid);
	clause_add_literal(node->children[i]);
	clause_add_literal(0);
    }
    crat_operation_count ++;
    crat_operation_clause_count += n;

    if (verb_level >= 3) {
	printf("Line %d.  Processed product %d addition\n", line_count, nid);
    }
    
}

void crat_add_sum(int cid) {
    token_t token = token_next();
    if (token != TOK_INT) {
	fprintf(ERROUT, "Expected operation number.  Got %s ('%s') instead\n", token_name[token], token_last);
	crat_error("crat_add_sum");
    } 
    int nid = token_value;
    node_t *node = node_new(NODE_SUM, nid, cid);
    node->children = ilist_new(2);
    node->dependency_list = ilist_new(1);
    ilist local_dependency_list = ilist_new(0);

    /* Get children */
    while (true) {
	token = token_next();
	if (token != TOK_INT) {
	    fprintf(ERROUT, "Expected sum operation argument.  Got '%s' instead\n", token_last);
	    crat_error("crat_add_sum");
	}
	int lit = token_value;
	int var = IABS(lit);
	node->children = ilist_push(node->children, lit);
	if (var <= input_variable_count) {
	    local_dependency_list = ilist_push(local_dependency_list, var);
	} else {
	    node_t *cnode = node_find(var);
	    if (cnode == NULL || cnode->type == NODE_NONE) {
		fprintf(ERROUT, "Can't add literal %d to node %d children.  Invalid node Id %d\n", lit, nid, var);
		crat_error("add_sum");
	    }
	    ilist save = node->dependency_list;
	    node->dependency_list = ilist_union(node->dependency_list, cnode->dependency_list);
	    ilist_free(save);
	}
	if (ilist_length(node->children) == 2)
	    break;
    }
    if (ilist_length(local_dependency_list) > 0) {
	ilist_sort(local_dependency_list);
	ilist save = node->dependency_list;
	node->dependency_list = ilist_union(node->dependency_list, local_dependency_list);
	ilist_free(save);
    }
    ilist_free(local_dependency_list);
    
    /* Prove mutual exclusion */
    lset_clear();
    lset_add_lit(node->children[0]);
    lset_add_lit(node->children[1]);
    rup_run();

    token_confirm_eol();

    /* Add sum clause */
    clause_new(cid);
    clause_add_literal(-nid);
    int i;
    int n = ilist_length(node->children);
    for (i = 0; i < n; i++)
	clause_add_literal(node->children[i]);
    clause_add_literal(0);
    for (i = 0; i < n; i++) {
	clause_new(cid+i+1);
	clause_add_literal(nid);
	clause_add_literal(-node->children[i]);
	clause_add_literal(0);
    }
    crat_operation_count ++;
    crat_operation_clause_count += n;

    if (verb_level >= 3) {
	printf("Line %d.  Processed sum %d addition\n", line_count, nid);
    }
    
}

void crat_delete_operation() {
    /* Skip for now */
    token_find_eol();
}

/* Check end condition.  Return literal representation of root node */
int crat_final_root() {
    /* First delete all of the clauses added for operations */
    int idx, nid, i;
    int root = 0;
    for (idx = 0; idx < node_asize; idx++) {
	nid = input_variable_count + idx + 1;
	node_t *node = node_find(nid);
	if (node == NULL || node->type == NODE_NONE)
	    continue;
	int n = ilist_length(node->children);
	for (i = 0; i <= n; i++)
	    clause_delete(node->cid + i);
    }
    clause_block_t *block = clause_set;
    while (block != NULL) {
	for (i = 0; i < block->length; i++) {
	    int cid = block->start_id + i;
	    int *lits = clause_locate(cid);
	    if (lits != NULL) {
		if (clause_is_unit(lits)) {
		    if (root == 0)
			root = *lits;
		    else {
			fprintf(ERROUT, "Found at least two root literals: %d and %d\n", root, *lits);
			crat_error("crat_final_root");
		    }
		} else {
		    fprintf(ERROUT, "Found undeleted, non-unit clause %d\n", cid);
		    crat_error("crat_final_root");
		}
	    }
	}
	block = block->next;
    }
    if (root == 0) {
	fprintf(ERROUT, "Didn't find root node\n");
	crat_error("crat_final_root");
    }
    return root;
}

void crat_read(char *fname) {
    token_setup(fname);
    /* Find and parse each command */
    while (true) {
	int cid = 0;
	token_t token = token_next();
	if (token == TOK_EOF)
	    break;
	if (token == TOK_STRING && token_last[0] == 'c') {
	    token_find_eol();
	    continue;
	} else if (token == TOK_INT) {
	    cid = token_value;
	    token = token_next();
	} 
	if (token != TOK_STRING) {
	    fprintf(ERROUT, "Expecting CRAT command.  Got '%s' (%s) instead\n", token_last, token_name[token]);
	    crat_error("crat_read");
	} else if (strcmp(token_last, "a") == 0)
	    crat_add_clause(cid);
	else if (strcmp(token_last, "dc") == 0)
	    crat_delete_clause();
	else if (strcmp(token_last, "p") == 0)
	    crat_add_product(cid);
	else if (strcmp(token_last, "s") == 0)
	    crat_add_sum(cid);
	else if (strcmp(token_last, "do") == 0)
	    crat_delete_operation();
	else {
	    fprintf(ERROUT, "Invalid CRAT command '%s'\n", token_last);
	    crat_error("crat_read");
	}
    }
    token_finish();
    if (verb_level >= 1) {
	int all_clause_count = crat_assertion_count + crat_operation_clause_count;
	printf("CHECK: Read CRAT file with %d operation,  %d+%d=%d clauses\n",
	       crat_operation_count, crat_assertion_count,
	       crat_operation_clause_count, all_clause_count);
	printf("CHECK: Deleted %d input and asserted clauses\n", crat_assertion_deletion_count);
    }
}

void run(char *cnf_name, char *crat_name) {
    double start = tod();
    cnf_read(cnf_name);
    if (verb_level >= 3)
	cnf_show(stdout);
    if (crat_name != NULL) {
	crat_read(crat_name);
	if (verb_level >= 3) {
	    crat_show(stdout);
	    printf("All clauses:\n");
	    clause_show_all(stdout);
	}
	int root = crat_final_root();
	if (verb_level >= 1) {
	    printf("CHECK: Final root literal %d\n", root);
	}
	printf("CHECK: SUCCESS.  CRAT representation verified\n");
    }
    if (verb_level >= 1) {
	double secs = tod() - start;
	printf("CHECK: Elapsed seconds: %.3f\n", secs);
    }
}

int main(int argc, char *argv[]) {
    char *cnf_name = NULL;
    char *crat_name = NULL;
    verb_level = 1;
    if (argc <= 1) 
	usage(argv[0]);
    int argi;
    char *istring;
    for (argi = 1; argi < argc && argv[argi][0] == '-'; argi++) {
	switch (argv[argi][1]) {
	case 'h':
	    usage(argv[0]);
	    break;
	case 'v':
	    istring = argv[++argi];
	    verb_level = atoi(istring);
	    break;
	default:
	    printf("Unknown command line option '%s'\n", argv[argi]);
	    usage(argv[0]);
	}
    }
    if (argi == argc) {
	printf("Require CNF file\n");
	usage(argv[0]);
    }
    cnf_name = argv[argi++];
    if (argi < argc) {
	crat_name = argv[argi++];
    }
    run(cnf_name, crat_name);
    return 0;
}
