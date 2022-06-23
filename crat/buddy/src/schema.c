/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
  This code is derived from the file 'kernel.c', part of the BuDDy BDD
  package authored and copywrited by Jorn Lind-Nielsen.  Permisssion
  to use the original code is subject to the terms noted below.

  Regarding the modifications, and subject to any constraints on the
  use of the original code, permission is hereby granted, free of
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

/*========================================================================
               Copyright (C) 1996-2002 by Jorn Lind-Nielsen
                            All rights reserved

    Permission is hereby granted, without written agreement and without
    license or royalty fees, to use, reproduce, prepare derivative
    works, distribute, and display this software and its documentation
    for any purpose, provided that (1) the above copyright notice and
    the following two paragraphs appear in all copies of the source code
    and (2) redistributions, including without limitation binaries,
    reproduce these notices in the supporting documentation. Substantial
    modifications to this software may be copyrighted by their authors
    and need not follow the licensing terms described here, provided
    that the new terms are clearly indicated in all files where they apply.

    IN NO EVENT SHALL JORN LIND-NIELSEN, OR DISTRIBUTORS OF THIS
    SOFTWARE BE LIABLE TO ANY PARTY FOR DIRECT, INDIRECT, SPECIAL,
    INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS
    SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE AUTHORS OR ANY OF THE
    ABOVE PARTIES HAVE BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

    JORN LIND-NIELSEN SPECIFICALLY DISCLAIM ANY WARRANTIES, INCLUDING,
    BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
    FITNESS FOR A PARTICULAR PURPOSE. THE SOFTWARE PROVIDED HEREUNDER IS
    ON AN "AS IS" BASIS, AND THE AUTHORS AND DISTRIBUTORS HAVE NO
    OBLIGATION TO PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
    MODIFICATIONS.
========================================================================*/

#include "config.h"
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <assert.h>

#include "schema.h"
#include "prime.h"

/*************************************************************************
  Various definitions and global variables
*************************************************************************/

/*=== INTERNAL DEFINITIONS =============================================*/

/* Min. number of nodes (%) that has to be left after a garbage collect
   unless a resize should be done. */
static int minfreenodes=20;


/*=== GLOBAL KERNEL VARIABLES ==========================================*/

int          schemarunning;            /* Flag - package initialized */
int          schemaerrorcond;          /* Some error condition */
int          schemanodesize;           /* Number of allocated nodes */
int          schemamaxnodesize;        /* Maximum allowed number of nodes */
int          schemamaxnodeincrease;    /* Max. # of nodes used to inc. table */
SchemaNode*     schemanodes;          /* All of the schema nodes */
static int          schemafreepos;        /* First free node */
static int          schemafreenum;        /* Number of free nodes */
long int     schemaproduced;       /* Number of new nodes ever produced */
int          schemainputvarnum;    /* Number of input variables */
int          schematotalvarnum;         /* Number of defined schema variables */
int*         schemarefstack;       /* Internal node reference stack */
int*         schemarefstacktop;    /* Internal node reference stack top */
jmp_buf      schemaexception;      /* Long-jump point for interrupting calc. */
int          schemaresized;        /* Flag indicating a resize of the nodetable */
schemaCacheStat schemacachestats;


/*=== PRIVATE KERNEL VARIABLES =========================================*/

static int      gbcollectnum;          /* Number of garbage collections */
static long int gbcclock;              /* Clock ticks used in GBC */
static schemainthandler  err_handler;     /* Error handler */
static schemagbchandler  gbc_handler;     /* Garbage collection handler */


   /* Strings for all error mesages */
static char *errorstrings[SCHEMA_ERRNUM] =
{ "Out of memory",
  "Unknown variable",
  "Value out of range",
  "Unknown schema root dereferenced",
  "schema_init() called twice",
  "File operation failed",
  "Incorrect file format",
  "User called break",
  "Cannot allocate fewer nodes than already in use",
  "Unknown operator",
  "Number of nodes reached user defined maximum",
  "Unknown schema - was not in node table",
  "Bad size argument",
  "Cannot (re)allocate ilist",
  "Cannot generate proof"
#endif
};


/*=== OTHER INTERNAL DEFINITIONS =======================================*/

#define NODEHASH(lvl,l,h) (TRIPLE(lvl,l,h) % schemanodesize)


/*************************************************************************
  SCHEMA misc. user operations
*************************************************************************/

int schema_init(int initnodesize, int varnum)
{
   int n, err;
   
   if (schemarunning)
      return schema_error(SCHEMA_RUNNING);
   
   schemanodesize = bdd_prime_gte(S_MAX(varnum, initnodesize)+1);
   
   if ((schemanodes=(SchemaNode*)malloc(sizeof(SchemaNode)*schemanodesize)) == NULL)
      return schema_error(SCHEMA_MEMORY);

   schemaresized = 0;
   
   /* Node 0 not used */
   schemanodes[0].type = SCHEMA_INVALID;
   schemanodes[0].refcou = S_MAXREF;
   schemanodes[0].mark = 0;
   schemanodes[0].arg1 = S_NULL;
   schemanodes[0].arg2 = S_NULL;
   schemanodes[0].xvar = 0;
   schemanodes[0].hash = 0;   
   schemanodes[0].next = -1;   

   /* Allocate nodes for input variables */
   for (n=1 ; n<=varnum ; n++)
   {
      schemanodes[n].type = SCHEMA_LIT;
      schemanodes[n].refcou = S_MAXREF;
      schemanodes[n].mark = 0;
      schemanodes[0].arg1 = S_NULL;
      schemanodes[0].arg2 = S_NULL;
      schemanodes[0].xvar = n;
      schemanodes[0].hash = n;   
      schemanodes[0].next = 0;
   }

   /* Set up unused nodes */
   for (n=varnum+1 ; n<schemanodesize ; n++)
   {
      schemanodes[n].type = SCHEMA_INVALID;
      schemanodes[n].refcou = 0;
      schemanodes[n].mark = 0;
      schemanodes[0].arg1 = S_NULL;
      schemanodes[0].arg2 = S_NULL;
      schemanodes[0].xvar = 0;
      schemanodes[0].hash = 0;   
      schemanodes[0].next = n+1;
   }
   schemanodes[schemanodesize-1].next = 0;

   schemafreepos = varnum+1;
   schemafreenum = schemanodesize-varnum-1;
   schemarunning = 1;
   schemainputvarnum = varnum;
   schematotalvarnum = varnum+1;
   gbcollectnum = 0;
   gbcclock = 0;
   schemamaxnodeincrease = DEFAULTMAXNODEINC;
   schemaerrorcond = 0;
   schema_gbc_hook(schema_default_gbchandler);
   schema_error_hook(schema_default_errhandler);
   
   if (setjmp(schemaexception) != 0)
      assert(0);

   return 0;
}


void schema_done(void)
{
   free(schemanodes);
   free(schemarefstack);
   
   schemanodes = NULL;
   schemarefstack = NULL;
   schemarunning = 0;
   schemanodesize = 0;
   schemamaxnodesize = 0;
   schemainputvarnum = 0;
   schematotalvarnum = 0;
   schemaproduced = 0;
   
   err_handler = NULL;
   gbc_handler = NULL;
}


schemainthandler schema_error_hook(schemainthandler handler)
{
   schemainthandler tmp = err_handler;
   err_handler = handler;
   return tmp;
}


void schema_clear_error(void)
{
   schemaerrorcond = 0;
}


schemagbchandler schema_gbc_hook(schemagbchandler handler)
{
   schemagbchandler tmp = gbc_handler;
   gbc_handler = handler;
   return tmp;
}
schema2inthandler schema_resize_hook(schema2inthandler handler)
{
   schema2inthandler tmp = handler;
   resize_handler = handler;
   return tmp;
}

int schema_setmaxincrease(int size)
{
   int old = schemamaxnodeincrease;
   
   if (size < 0)
      return schema_error(SCHEMA_SIZE);

   schemamaxnodeincrease = size;
   return old;
}

int schema_setmaxnodenum(int size)
{
   if (size > schemanodesize  ||  size == 0)
   {
      int old = schemamaxnodesize;
      schemamaxnodesize = size;
      return old;
   }

   return schema_error(SCHEMA_NODES);
}

int schema_setminfreenodes(int mf)
{
   int old = minfreenodes;
   
   if (mf<0 || mf>100)
      return schema_error(SCHEMA_RANGE);

   minfreenodes = mf;
   return old;
}

int schema_getnodenum(void)
{
    return schemanodesize - schemafreenum;
}

int schema_getallocnum(void)
{
   return schemanodesize;
}

int schema_isrunning(void)
{
   return schemarunning;
}


void schema_stats(schemaStat *s)
{
   s->produced = schemaproduced;
   s->nodenum = schemanodesize;
   s->maxnodenum = schemamaxnodesize;
   s->freenodes = schemafreenum;
   s->minfreenodes = minfreenodes;
   s->varnum = schemavarnum;
   s->gbcnum = gbcollectnum;
}


/*************************************************************************
  Error handler
*************************************************************************/

const char *schema_errstring(int e)
{
   e = abs(e);
   if (e<1 || e>SCHEMA_ERRNUM)
      return NULL;
   return errorstrings[e-1];
}


void schema_default_errhandler(int e)
{
    const char *s = schema_errstring(e);
    if (s == NULL)
	fprintf(ERROUT, "SCHEMA error.  Unknown error code %d\n", e);
    else
	fprintf(ERROUT, "SCHEMA error: %s\n", schema_errstring(e));
    exit(1);
}


int schema_error(int e)
{
   if (err_handler != NULL)
      err_handler(e);
   
   return e;
}


/*************************************************************************
  SCHEMA primitives
*************************************************************************/

SCHEMA schema_one(void)
{
    return S_ONE;
}

SCHEMA schema_zero(void)
{
    return S_ZERO;
}

SCHEMA schema_from_variable(int v)
{
    if (v < 1 || v > schemainputvarnum)
	schema_error(SCHEMA_VAR);
    return (SCHEMA) v;
}


schema_type_t schema_type(SCHEMA root) {
    S_CHECKa(root, SCHEMA_INVALID);
    return S_TYPE(root);
}

SCHEMA schema_arg1(SCHEMA root) {
    S_CHECKa(root, SCHEMA_INVALID);
    return S_TYPE(root);
}

SCHEMA schema_arg2(SCHEMA root) {
    S_CHECKa(root, SCHEMA_INVALID);
    return S_TYPE(root);
}

int schema_xvar(SCHEMA root) {
    S_CHECKa(root, SCHEMA_INVALID);
    return S_XVAR(root);
}

SCHEMA schema_not(SCHEMA root) {
    S_CHECK(S_GETNODE(root));
    return -root;
}


/*************************************************************************
  Garbage collection and node referencing
*************************************************************************/

void schema_default_gbchandler(int pre, schemaGbcStat *s)
{
   if (!pre)
   {
      printf("c Schema Garbage collection #%d: %d nodes / %d free / %d previously freed ",
	     s->num, s->nodes, s->freenodes, s->prevfreednodes);
      printf(" / %.1fs / %.1fs total\n",
	     (float)s->time/(float)(CLOCKS_PER_SEC),
	     (float)s->sumtime/(float)CLOCKS_PER_SEC);
   }
}


static void schema_gbc_rehash(void)
{
   int n;

   schemafreepos = 0;
   schemafreenum = 0;

   for (n=schemanodesize-1 ; n>=2 ; n--)
   {
      register SchemaNode *node = &schemanodes[n];

      if (LOWp(node) != -1)
      {
	 register unsigned int hash;

	 hash = NODEHASH(LEVELp(node), LOWp(node), HIGHp(node));
	 node->next = schemanodes[hash].hash;
	 schemanodes[hash].hash = n;
      }
      else
      {
	 node->next = CHECKNODE(schemafreepos);
	 schemafreepos = CHECKNODE(n);
	 CHECKRANGE(schemafreenum++);
      }
   }
}

/* NEEDS WORK */
void schema_gbc(void)
{
   int *r;
   int n;
   long int c2, c1 = clock();
   int freed = 0;

   if (gbc_handler != NULL)
   {
      schemaGbcStat s;
      s.nodes = schemanodesize;
      s.freenodes = schemafreenum;
      s.time = 0;
      s.sumtime = gbcclock;
      s.num = gbcollectnum;
      gbc_handler(1, &s);
   }
   
   for (r=schemarefstack ; r<schemarefstacktop ; r++) {
       schema_mark(*r);
   }

   for (n=0 ; n<schemanodesize ; n++)
   {
       if (schemanodes[n].refcou > 0) {
	   schema_mark(n);
       }
      schemanodes[n].hash = 0;
   }
   
   schemafreepos = 0;
   schemafreenum = 0;

   for (n=schemanodesize-1 ; n>=2 ; n--)
   {
      register SchemaNode *node = &schemanodes[n];

      if ((LEVELp(node) & MARKON)  &&  LOWp(node) != -1)
      {
	 register unsigned int hash;

	 LEVELp(node) &= MARKOFF;
	 hash = NODEHASH(LEVELp(node), LOWp(node), HIGHp(node));
	 node->next = schemanodes[hash].hash;
	 schemanodes[hash].hash = n;
      }
      else
      {
	 if (LOWp(node) != S_NULL)
	     freed++;

	 LOWp(node) = -1;
	 node->next = CHECKNODE(schemafreepos);
	 schemafreepos = CHECKNODE(n);
	 CHECKRANGE(schemafreenum++);
      }
   }

   c2 = clock();
   gbcclock += c2-c1;
   gbcollectnum++;


   if (gbc_handler != NULL)
   {
      schemaGbcStat s;
      s.nodes = schemanodesize;
      s.freenodes = schemafreenum;
      s.time = c2-c1;
      s.sumtime = gbcclock;
      s.num = gbcollectnum;
      s.prevfreednodes = freed;
      gbc_handler(0, &s);
   }
}

SCHEMA schema_addref(SCHEMA root)
{
   SCHEMA troot = S_GETNODE(root);
   if (troot <= schemaintputvarnum || IS_ONE(troot) || !schemarunning)
      return root;
   if (troot >= schemanodesize)
      return schema_error(SCHEMA_ILLSCHEMA);
   if (S_TYPE(troot) == SCHEMA_INVALID)
      return schema_error(SCHEMA_ILLSCHEMA);

   INCREF(troot);
   return root;
}

SCHEMA schema_delref(SCHEMA root)
{
    SCHEMA troot = S_GETNODE(root);
    if (troot <= schemainputvarnum  || IS_ONE(troot) ||  !schemarunning)
      return root;
   if (troot >= schemanodesize)
      return schema_error(SCHEMA_ILLSCHEMA);
   if (S_TYPE(troot) == SCHEMA_INVALID)
      return schema_error(SCHEMA_ILLSCHEMA);

   /* if the following line is present, fails there much earlier */ 
   if (!HASREF(troot)) schema_error(SCHEMA_BREAK); /* distinctive */
   
   DECREF(troot);
   return root;
}


/*=== RECURSIVE MARK / UNMARK ==========================================*/

void bdd_mark(int i)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];
   if (LEVELp(node) & MARKON  ||  LOWp(node) == -1)
      return;
   
   LEVELp(node) |= MARKON;
   
   bdd_mark(LOWp(node));
   bdd_mark(HIGHp(node));
}


void bdd_mark_upto(int i, int level)
{
   BddNode *node = &bddnodes[i];
   
   if (i < 2)
      return;
   
   if (LEVELp(node) & MARKON  ||  LOWp(node) == -1)
      return;
   
   if (LEVELp(node) > level)
      return;

   LEVELp(node) |= MARKON;

   bdd_mark_upto(LOWp(node), level);
   bdd_mark_upto(HIGHp(node), level);
}


void bdd_markcount(int i, int *cou)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];
   if (MARKEDp(node)  ||  LOWp(node) == -1)
      return;
   
   SETMARKp(node);
   *cou += 1;
   
   bdd_markcount(LOWp(node), cou);
   bdd_markcount(HIGHp(node), cou);
}


void bdd_unmark(int i)
{
   BddNode *node;
   
   if (i < 2)
      return;

   node = &bddnodes[i];

   if (!MARKEDp(node)  ||  LOWp(node) == -1)
      return;
   UNMARKp(node);
   
   bdd_unmark(LOWp(node));
   bdd_unmark(HIGHp(node));
}


void bdd_unmark_upto(int i, int level)
{
   BddNode *node = &bddnodes[i];

   if (i < 2)
      return;
   
   if (!(LEVELp(node) & MARKON))
      return;
   
   LEVELp(node) &= MARKOFF;
   
   if (LEVELp(node) > level)
      return;

   bdd_unmark_upto(LOWp(node), level);
   bdd_unmark_upto(HIGHp(node), level);
}


/*************************************************************************
  Unique node table functions
*************************************************************************/

int bdd_makenode(unsigned int level, int low, int high)
{
   register BddNode *node;
   register unsigned int hash;
   register int res;

#ifdef CACHESTATS
   bddcachestats.uniqueAccess++;
#endif
   
      /* check whether children are equal */
   if (low == high)
      return low;

      /* Try to find an existing node of this kind */
   hash = NODEHASH(level, low, high);
   res = bddnodes[hash].hash;

   while(res != 0)
   {
      if (LEVEL(res) == level  &&  LOW(res) == low  &&  HIGH(res) == high)
      {
#ifdef CACHESTATS
	 bddcachestats.uniqueHit++;
#endif
	 return res;
#if DO_TRACE && ENABLE_TBDD
	 if (NNAME(res) == TRACE_NNAME)
	     printf("Found node N%d in unique table\n", TRACE_NNAME);
#endif 	 
      }

      res = CHECKNODE(bddnodes[res].next);
#ifdef CACHESTATS
      bddcachestats.uniqueChain++;
#endif
   }
   
   /* Error checking */
   if (level >= LEVEL(low))
   {
       fprintf(ERROUT, "Attempt to create invalid BDD node.  New Level = %d.  Low node level = %d\n", level, LEVEL(low));
       bdd_error(BDD_ILLBDD);
       return 0;
   }

   if (level >= LEVEL(high))
   {
       fprintf(ERROUT, "Attempt to create invalid BDD node.  New Level = %d.  High node level = %d\n", level, LEVEL(high));
       bdd_error(BDD_ILLBDD);
       return 0;
   }

      /* No existing node -> build one */
#ifdef CACHESTATS
   bddcachestats.uniqueMiss++;
#endif

      /* Any free nodes to use ? */
   if (bddfreepos == 0)
   {
      if (bdderrorcond)
	 return 0;
      
         /* Try to allocate more nodes */
      bdd_gbc();

      if (CHECKRANGE(bddnodesize-bddfreenum) >= usednodes_nextreorder  &&
	  bdd_reorder_ready())
      {
	 longjmp(bddexception,1);
      }

      if ((bddfreenum*100) / bddnodesize <= minfreenodes)
      {
	 bdd_noderesize(1);
	 hash = NODEHASH(level, low, high);
      }

         /* Panic if that is not possible */
      if (bddfreepos == 0)
      {
	 bdd_error(BDD_NODENUM);
	 bdderrorcond = abs(BDD_NODENUM);
	 return 0;
      }
   }

      /* Build new node */
   res = CHECKNODE(bddfreepos);
   bddfreepos = CHECKNODE(bddnodes[bddfreepos].next);
   CHECKRANGE(bddfreenum--);
   bddproduced++;
   
   node = &bddnodes[res];
   LEVELp(node) = level;
   LOWp(node) = low;
   HIGHp(node) = high;
   
   #if ENABLE_TBDD
   if (level > 0) {
       if (proof_type == PROOF_NONE) {
	   XVARp(node) = res;
	   DCLAUSEp(node) = 0;
       } else {
	   int nid = ++(*variable_counter);
	   int vid = bdd_level2var(level);
	   int hid = XVAR(high);
	   int lid = XVAR(low);
	   int hname = NNAME(high);
	   int lname = NNAME(low);
	   int dbuf[3+ILIST_OVHD];
	   int abuf[2+ILIST_OVHD];
	   ilist dlist = ilist_make(dbuf, 3);
	   ilist alist = ilist_make(abuf, 2);
	   int huid, luid;
	   XVARp(node) = nid;
	   DCLAUSEp(node) = *clause_id_counter + 1;
	   print_proof_comment(2, "Defining clauses for node N%d = ITE(V%d (level=%d), N%d, N%d)", nid, vid, level, hname, lname);
	   huid = generate_clause(defining_clause(dlist, DEF_HU, nid, vid, hid, lid), alist);
	   luid = generate_clause(defining_clause(dlist, DEF_LU, nid, vid, hid, lid), alist);
	   if (huid != TAUTOLOGY)
	       ilist_push(alist, -huid);
	   if (luid != TAUTOLOGY)
	       ilist_push(alist, -luid);
	   generate_clause(defining_clause(dlist, DEF_HD, nid, vid, hid, lid), alist);              
	   generate_clause(defining_clause(dlist, DEF_LD, nid, vid, hid, lid), alist);       
       }
   }
   #endif
      /* Insert node */
   node->next = bddnodes[hash].hash;
   bddnodes[hash].hash = res;

#if DO_TRACE && ENABLE_TBDD
	 if (NNAME(res) == TRACE_NNAME)
	     printf("TRACE: Added node N%d to unique table\n", TRACE_NNAME);
#endif 	 
   return res;
}


int bdd_noderesize(int doRehash)
{
   BddNode *newnodes;
   int oldsize = bddnodesize;
   int n;

   if (bddnodesize >= bddmaxnodesize  &&  bddmaxnodesize > 0)
      return -1;
   
   bddnodesize = bddnodesize << 1;

   if (bddnodesize > oldsize + bddmaxnodeincrease)
      bddnodesize = oldsize + bddmaxnodeincrease;

   if (bddnodesize > bddmaxnodesize  &&  bddmaxnodesize > 0)
      bddnodesize = bddmaxnodesize;

   bddnodesize = bdd_prime_lte(bddnodesize);
   
   if (resize_handler != NULL)
      resize_handler(oldsize, bddnodesize);

   newnodes = (BddNode*)realloc(bddnodes, sizeof(BddNode)*bddnodesize);
   if (newnodes == NULL)
      return bdd_error(BDD_MEMORY);
   bddnodes = newnodes;

   if (doRehash)
      for (n=0 ; n<oldsize ; n++)
	 bddnodes[n].hash = 0;
   
   for (n=oldsize ; n<bddnodesize ; n++)
   {
      bddnodes[n].refcou = 0;
      bddnodes[n].hash = 0;
      LEVEL(n) = 0;
      LOW(n) = -1;
      bddnodes[n].next = n+1;
   }
   bddnodes[bddnodesize-1].next = CHECKNODE(bddfreepos);
   bddfreepos = CHECKNODE(oldsize);
   bddfreenum += CHECKRANGE(bddnodesize - oldsize);

   if (doRehash)
      bdd_gbc_rehash();

   bddresized = 1;
   return 0;
}


void bdd_checkreorder(void)
{
   bdd_reorder_auto();

      /* Do not reorder before twice as many nodes have been used */
   usednodes_nextreorder = 2 * (bddnodesize - bddfreenum);
   
      /* And if very little was gained this time (< 20%) then wait until
       * even more nodes (upto twice as many again) have been used */
   if (bdd_reorder_gain() < 20)
      usednodes_nextreorder +=
	 (usednodes_nextreorder * (20-bdd_reorder_gain())) / 20;
}


/*************************************************************************
  Variable sets
*************************************************************************/

/*
NAME    {* bdd\_scanset *}
SECTION {* kernel *}
SHORT   {* returns an integer representation of a variable set *}
PROTO   {* int bdd_scanset(BDD r, int **v, int *n) *}
DESCR   {* Scans a variable set {\tt r} and copies the stored variables into
           an integer array of variable numbers. The argument {\tt v} is
	   the address of an integer pointer where the array is stored and
	   {\tt n} is a pointer to an integer where the number of elements
	   are stored. It is the users responsibility to make sure the
	   array is deallocated by a call to {\tt free(v)}. The numbers
	   returned are guaranteed to be in ascending order. *}
ALSO    {* bdd\_makeset *}
RETURN  {* Zero on success, otherwise a negative error code. *}
*/
int bdd_scanset(BDD r, int **varset, int *varnum)
{
   int n, num;

   CHECK(r);
   if (r < 2)
   {
      *varnum = 0;
      *varset = NULL;
      return 0;
   }
   
   for (n=r, num=0 ; n > 1 ; n=HIGH(n))
      num++;

   if (((*varset) = (int *)malloc(sizeof(int)*num)) == NULL)
      return bdd_error(BDD_MEMORY);
   
   for (n=r, num=0 ; n > 1 ; n=HIGH(n))
      (*varset)[num++] = bddlevel2var[LEVEL(n)];

   *varnum = num;

   return 0;
}


/*
NAME    {* BDD\_makeset *}
SECTION {* kernel *}
SHORT   {* builds a BDD variable set from an integer array *}
PROTO   {* BDD BDD_makeset(int *v, int n) *}
DESCR   {* Reads a set of variable numbers from the integer array {\tt v}
           which must hold exactly {\tt n} integers and then builds a BDD
	   representing the variable set.

	   The BDD variable set is represented as the conjunction of
	   all the variables in their positive form and may just as
	   well be made that way by the user. The user should keep a
	   reference to the returned BDD instead of building it every
	   time the set is needed. *}
ALSO    {* bdd\_scanset *}
RETURN {* A BDD variable set. *} */
BDD BDD_makeset(int *varset, int varnum)
{
   int v, res=1;
   
   for (v=varnum-1 ; v>=0 ; v--)
   {
      BDD tmp;
      bdd_addref(res);
      tmp = bdd_apply(res, BDD_ithvar(varset[v]), bddop_and);
      bdd_delref(res);
      res = tmp;
   }

   return res;
}

/* EOF */
