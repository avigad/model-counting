#ifndef _TBDD_H
#define _TBDD_H

/* Turn on TBDD-specific information in files */
#ifndef ENABLE_TBDD
#define ENABLE_TBDD 1
#endif

/* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

/*============================================
 API for trusted extension to BuDDy BDD package
============================================*/


#include <limits.h>
#include "ilist.h"
#include "bdd.h"

/* Value representing logical truth */
#define TAUTOLOGY INT_MAX 

/* 
   A trusted BDD is one for which a proof has
   been generated showing that it is logically
   entailed by a set of input clauses.

   It's structurally identical to a proof-carrying BDD, but with
   an enhanced interpretation.

   All copies of a TBDD build on single reference to root node.
   Final deletion should occur when TBDD no longer needed in proof.

*/
typedef pcbdd tbdd;

#ifdef CPLUSPLUS
extern "C" {
#endif


/*============================================
  Package setup.
============================================*/

/* 
  Set up package.  Arguments:
  - proof output file
  - number of variables in CNF

  When generating LRAT proofs, also require arguments:
  - Number of clauses in CNF
  - The list of clauses, where clause i is at clauses[i-1]
  
  These functions also initialize BuDDy, using parameters tuned according
  to the predicted complexity of the operations.

  Return 0 if OK, otherwise error code
*/

/* Supported proof types */
   typedef enum { PROOF_LRAT, PROOF_DRAT, PROOF_FRAT, PROOF_NONE } proof_type_t;

   extern int tbdd_init(FILE *pfile, int *variable_counter, int *clause_id_counter, ilist *input_clauses, ilist variable_ordering, proof_type_t ptype, bool binary);

/* 
   Initializers specific for the seven combinations of proof formats
 */
extern int tbdd_init_lrat(FILE *pfile, int variable_count, int clause_count, ilist *input_clauses, ilist variable_ordering);
extern int tbdd_init_lrat_binary(FILE *pfile, int variable_count, int clause_count, ilist *input_clauses, ilist variable_ordering);
extern int tbdd_init_drat(FILE *pfile, int variable_count);
extern int tbdd_init_drat_binary(FILE *pfile, int variable_count);
extern int tbdd_init_frat(FILE *pfile, int *variable_counter, int *clause_id_counter);
extern int tbdd_init_frat_binary(FILE *pfile, int *variable_counter, int *clause_id_counter);
extern int tbdd_init_noproof(int variable_count);

/*
  Deallocate all resources used by TBDD.
  If verbosity >= 1, print summary information
 */
extern void tbdd_done();

/*
  Functions that can be added to provide more data on exit.
  Function takes verbosity level as argument.
 */
typedef void (*tbdd_info_fun)(int);

void tbdd_add_info_fun(tbdd_info_fun f);

typedef void (*tbdd_done_fun)(void);

void tbdd_add_done_fun(tbdd_done_fun f);

/*
  Setting optional solver features
 */

/* Verbosity levels:

   0: Totally silent
   1: Summary information (default)
   2: Enable comments in generated proof
   3: Debugging information
*/
extern void tbdd_set_verbose(int level);

/*============================================
 Creation and manipulation of trusted BDDs
============================================*/

/*
 Call to delete TBDD when no longer needed for
 any inferences.  Will decrement reference count
 and delete unit clause
*/
extern void tbdd_delete(tbdd tr);

/* 
   proof_step = TAUTOLOGY
   root = 1
 */
extern tbdd tbdd_tautology();

/* 
   proof_step = TAUTOLOGY
   root = 0 (Used as an error return)
 */

extern tbdd tbdd_null();

/*
   Test whether underlying BDD is 0/1
 */
extern bool tbdd_is_true(tbdd tr);
extern bool tbdd_is_false(tbdd tr);

/*
  Generate BDD representation of specified input clause.
  Generate proof that BDD will evaluate to TRUE
  for all assignments satisfying clause.

  clause_id should be number between 1 and the number of input clauses
 */

extern tbdd tbdd_from_clause(ilist clause);  // For DRAT
extern tbdd tbdd_from_clause_id(int id);     // For LRAT

/*
  Generate BDD representation of XOR.
  For DRAT
 */
extern tbdd tbdd_from_xor(ilist variables, int phase);

/* Operations on TBDDs */
extern tbdd      tbdd_and(tbdd, tbdd);

/*
  Upgrade ordinary BDD to TBDD by proving
  implication from another TBDD
 */
extern tbdd tbdd_validate(BDD r, tbdd tr);

/*
  Declare BDD to be trustworthy.  Proof
  checker must provide validation.
  Only works when generating DRAT proofs
 */
extern tbdd tbdd_trust(BDD r);

/*
  Form conjunction of two TBDDs and prove
  their conjunction implies the new one
 */
extern tbdd tbdd_and(tbdd tr1, tbdd tr2);

/*
  Form conjunction of TBDDs tl & tr.  Use to validate
  BDD r
 */
extern tbdd tbdd_validate_with_and(BDD r, tbdd tl, tbdd tr);

/*
  Validate that a clause is implied by a TBDD.
  Use this version when generating LRAT proofs
  Returns clause id.
 */
extern int tbdd_validate_clause(ilist clause, tbdd tr);

/*
  Assert that a clause holds.  Proof checker
  must provide validation.
  Use this version when generating DRAT proofs,
  or when don't want to provide antecedent in FRAT proof
  Returns clause id.
 */
extern int assert_clause(ilist clause);

/*============================================
 Useful BDD operations
============================================*/

/* Construct BDD representation of a clause */
extern BDD BDD_build_clause(ilist literals);
/* Construct BDD representation of XOR (phase = 1) or XNOR (phase = 0) */
extern BDD BDD_build_xor(ilist variables, int phase);

/* Represent conjunction of literals (a "cube") as a BDD or an ilist */
extern BDD BDD_build_cube(ilist literals);
extern ilist BDD_decode_cube(BDD r);

#ifdef CPLUSPLUS
}
#endif

#ifdef CPLUSPLUS
extern "C" {
/*
  Upgrade ordinary BDD to TBDD by proving
  implication from another TBDD
 */
inline tbdd tbdd_validate(bdd r, tbdd tr) { return tbdd_validate(r.get_BDD(), tr); }

/*
  Declare BDD to be trustworthy.  Proof
  checker must provide validation.
  Only works when generating DRAT proofs
 */
inline tbdd tbdd_trust(bdd r) { return tbdd_trust(r.get_BDD()); }

/*
  Form conjunction of TBDDs tl & tr.  Use to validate
  BDD r
 */
inline tbdd tbdd_validate_with_and(bdd r, tbdd tl, tbdd tr) { return tbdd_validate_with_and(r.get_BDD(), tl, tr); }

/* Construct BDD representation of a clause */
inline bdd bdd_build_clause(ilist literals) { return bdd(BDD_build_clause(literals)); }
/* Construct BDD representation of XOR (phase = 1) or XNOR (phase = 0) */

inline bdd bdd_build_xor(ilist variables, int phase) { return bdd(BDD_build_xor(variables, phase)); }

/* Represent conjunction of literals (a "cube") as a BDD or an ilist */
inline bdd bdd_build_cube(ilist literals) { return bdd(BDD_build_cube(literals)); }
inline ilist bdd_decode_cube(BDD r) { return BDD_decode_cube(r.get_BDD()); }
}
#else /* !C++ */
#endif
#endif /* _TBDD_H */
/* EOF */


