/*========================================================================
  Copyright (c) 2022 Randal E. Bryant, Carnegie Mellon University
  
  This code is derived from the files 'kernel.h' and 'bdd.h', parts of
  the BuDDy BDD package authored and copywrited by Jorn Lind-Nielsen.
  Permisssion to use the original code is subject to the terms noted
  below.

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

#ifndef _SCHEMA_H
#define _SCHEMA_H

   /* Allow this headerfile to define C++ constructs if requested */
#ifdef __cplusplus
#define CPLUSPLUS
#endif

/*=== Includes =========================================================*/

#include <limits.h>
#include <stdio.h>
#include <stdbool.h>
#include <setjmp.h>

/*=== Error message destination ===*/
#define ERROUT stdout

/*=== Data types =========================================================*/

typedef int SCHEMA;

#ifndef CPLUSPLUS
typedef BDD schema;
#endif /* CPLUSPLUS */


typedef enum { SCHEMA_CONST, SCHEMA_LIT, SCHEMA_CONJ, SCHEMA_DISJ, SCHEMA_INVALID, SCHEMA_COUNT } schema_type_t;

/*=== Constants =========================================================*/

#define S_ONE INT_MAX
#define S_ZERO (-S_ONE)

/* Unused node argument */
#define S_NULL 0

/*=== Status information ===============================================*/

typedef struct s_schemaStat
{
   long int produced;
   int nodenum;
   int maxnodenum;
   int freenodes;
   int minfreenodes;
   int varnum;
   int gbcnum;
} schemaStat;

typedef struct s_schemaGbcStat
{
   int nodes;
   int freenodes;
   int prevfreednodes;
   long time;
   long sumtime;
   int num;
} schemaGbcStat;


/*=== SANITY CHECKS ====================================================*/

   /* Make sure we use at least 32 bit integers */
#if (INT_MAX < 0x7FFFFFFF)
#error The compiler does not support 4 byte integers!
#endif


   /* Sanity check argument and return eventual error code */
#define S_CHECK(r)\
   if (!schemarunning) return schema_error(SCHEMA_RUNNING);\
   else if ((r) < 1  || ((r) >= schemanodesize && (r) != S_ONE)) return schema_error(SCHEMA_ILLSCHEMA);

   /* Sanity check argument and return eventually the argument 'a' */
#define S_CHECKa(r,a)\
   if (!schemarunning) { schema_error(SCHEMA_RUNNING); return (a); }\
   else if ((r) < 1  ||  ((r) >= schemanodesize && (r) != S_ONE)) 	\
     { schema_error(SCHEMA_ILLSCHEMA); return (a); }

   /* Sanity check argument and return */
#define S_CHECKn(r)\
   if (!schemarunning) return schema_error(SCHEMA_RUNNING);\
   else if ((r) < 1  || ((r) >= schemanodesize && (r) != S_ONE)) \
       { schema_error(SCHEMA_ILLSCHEMA); return; }

/*=== SEMI-INTERNAL TYPES ==============================================*/

typedef struct s_SchemaNode /* Node table entry */
{
   schema_type_t type  :  3;
   unsigned int refcou : 28;
   unsigned int mark   :  1;
   int arg1;
   int arg2;
   int xvar;     /* Associated extension variable */
   int hash;
   int next;
} SchemaNode;


/*=== SCHEMA VARIABLES =================================================*/

#ifdef CPLUSPLUS
extern "C" {
#endif

extern int       schemarunning;         /* Flag - package initialized */
extern int       schemaerrorcond;       /* Some error condition was met */
extern int       schemanodesize;        /* Number of allocated nodes */
extern int       schemamaxnodesize;     /* Maximum allowed number of nodes */
extern int       schemamaxnodeincrease; /* Max. # of nodes used to inc. table */
extern SchemaNode*  schemanodes;        /* All of the schema nodes */
extern int       schemainputvarnum;     /* Number of input variables */
extern int       schematotalvarnum;     /* Number of input+extension variables */
extern int*      schemarefstack;        /* Internal node reference stack */
extern int*      schemarefstacktop;     /* Internal node reference stack top */
extern jmp_buf   schemaexception;
extern int       schemaresized;
extern schemaCacheStat schemacachestats;

#ifdef CPLUSPLUS
}
#endif


/*=== SCHEMA DEFINITIONS ===============================================*/

#define S_MIN(a,b) ((a) < (b) ? (a) : (b))
#define S_MAX(a,b) ((a) > (b) ? (a) : (b))
#define S_ABS(a) ((a)<0?-(a):(a))
#define S_NEW(t,n) ( (t*)malloc(sizeof(t)*(n)) )

/* Test whether negated */
#define S_NEGATED(r) ((n)<0)
/* Extract node id */
#define S_GETNODE(r) (S_ABS(r))

/* 
   28 bits allocated for reference count
 */
#define S_MAXREF 0xFFFFFFF

   /* Reference counting */
#define S_DECREF(n) if (schemanodes[n].refcou!=S_MAXREF && schemanodes[n].refcou>0) schemanodes[n].refcou--
#define S_INCREF(n) if (schemanodes[n].refcou<S_MAXREF) schemanodes[n].refcou++
#define S_DECREFp(n) if (n->refcou!=S_MAXREF && n->refcou>0) n->refcou--
#define S_INCREFp(n) if (n->refcou<S_MAXREF) n->refcou++
#define S_HASREF(n) (schemanodes[n].refcou > 0)

   /* Marking SCHEMA nodes */
#define S_SETMARK(n)  (schemanodes[n].mark = 1)
#define S_UNMARK(n)   (schemanodes[n].mark = 0)
#define S_MARKED(n)   (schemanodes[n].mark)
#define S_SETMARKp(p) (node->mark = 1)
#define S_UNMARKp(p)  (node->mark = 0)
#define S_MARKEDp(p)  (node->mark)

   /* Hashfunctions */

#define S_PAIR(a,b)      ((unsigned int)((((unsigned int)a)+((unsigned int)b))*(((unsigned int)a)+((unsigned int)b)+((unsigned int)1))/((unsigned int)2)+((unsigned int)a)))
#define S_TRIPLE(a,b,c)  ((unsigned int)(PAIR((unsigned int)c,PAIR(a,b))))

   /* Inspection of SCHEMA ids */
#define S_ISCONST(s)    (S_GETNODE(s)!=S_ONE)
#define S_ISNONCONST(s) (S_GETNODE(s)!=S_ONE)
#define S_ISONE(s)      ((s) == S_ONE)
#define S_ISZERO(s)     ((s) == S_ZERO)
#define S_ISVAR(s)      ((s) > 0 && (s) <= schemainputvarnum)
#define S_ISLIT(s)      (S_IS_LIT(S_GETNODE(s)))

   /* Inspection of SCHEMA nodes */
#define S_TYPE(a)     (schemanodes[a].type)
#define S_ARG1(a)     (schemanodes[a].arg1)
#define S_ARG2(a)     (schemanodes[a].arg1)
#define S_XVAR(a)     (schemanodes[a].xvar)
#define S_TYPEp(a)    ((p)->type)
#define S_ARG1p(a)    ((p)->arg1)
#define S_ARG2p(a)    ((p)->arg1)
#define S_XVARp(a)    ((p)->xvar)

   /* Stacking for garbage collector */
#define S_INITREF    schemarefstacktop = schemarefstack
#define S_PUSHREF(a) *(schemarefstacktop++) = (a)
#define S_READREF(a) *(schemarefstacktop-(a))
#define S_POPREF(a)  schemarefstacktop -= (a)

#define S_DEFAULTMAXNODEINC 50000


/*=== SCHEMA PROTOTYPES ================================================*/

#ifdef CPLUSPLUS
extern "C" {
#endif

extern int      schema_init(int, int);
extern void     schema_done(void);
extern int      schema_isrunning(void);
extern int      schema_setmaxnodenum(int);
extern int      schema_setmaxincrease(int);
extern int      schema_setminfreenodes(int);
extern int      schema_getnodenum(void);
extern int      schema_getallocnum(void);
extern void     schema_stats(schemaStat *);
extern void     schema_default_gbchandler(int, schemaGbcStat *);
extern void     schema_default_errhandler(int);
extern const char *schema_errstring(int);
extern void     schema_clear_error(void);
extern int    schema_error(int);

extern SCHEMA  schema_makenode(schema_type_t, int, int);
extern int    schema_noderesize(int);
extern void   schema_mark(int);
extern void   schema_mark_upto(int, int);
extern void   schema_markcount(int, int*);
extern void   schema_unmark(int);
extern void   schema_unmark_upto(int, int);

extern SCHEMA schema_addref(SCHEMA);
extern SCHEMA schema_delref(SCHEMA);
extern void   schema_gbc(void);

extern schema_type_t schema_type(SCHEMA);
extern SCHEMA schema_arg1(SCHEMA);
extern SCHEMA schema_arg2(SCHEMA);
extern int    schema_xvar(SCHEMA);

extern SCHEMA schema_not(SCHEMA);
extern SCHEMA schema_or(SCHEMA, SCHEMA);
extern SCHEMA schema_and(SCHEMA, SCHEMA);
extern SCHEMA schema_ite(SCHEMA, SCHEMA, SCHEMA);

#ifndef CPLUSPLUS
extern SCHEMA schema_one(void);
extern SCHEMA schema_zero(void);
extern SCHEMA schema_from_variable(int v);
#endif


#ifdef CPLUSPLUS
}
#endif

/*=== Error codes ======================================================*/

#define SCHEMA_MEMORY (-1)   /* Out of memory */
#define SCHEMA_VAR (-2)      /* Unknown variable */
#define SCHEMA_RANGE (-3)    /* Variable value out of range (not in domain) */
#define SCHEMA_DEREF (-4)    /* Removing external reference to unknown node */
#define SCHEMA_RUNNING (-5)  /* Called schema_init() twice whithout schema_done() */
#define SCHEMA_FILE (-6)     /* Some file operation failed */
#define SCHEMA_FORMAT (-7)   /* Incorrect file format */
#define SCHEMA_BREAK (-8)    /* User called break */
#define SCHEMA_NODES (-9)   /* Tried to set max. number of nodes to be fewer */
                          /* than there already has been allocated */
#define SCHEMA_OP (-10)      /* Unknown operator */
#define SCHEMA_NODENUM (-11) /* Number of nodes reached user defined maximum */
#define SCHEMA_ILLSCHEMA (-12)  /* Illegal schema argument */
#define SCHEMA_SIZE (-13)    /* Illegal size argument */

#define ILIST_ALLOC (-14)  /* Invalid allocation for ilist */
#define SCHEMA_PROOF (-15)   /* Couldn't complete proof of justification */
#define SCHEMA_ERRNUM 15

#endif /* _SCHEMA_H */


/* EOF */
