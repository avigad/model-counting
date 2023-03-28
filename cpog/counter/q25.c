#include <stdlib.h>
#include <string.h>
#include "q25.h"

/*
   Declarations.  The program assumes that computation is performed in decimal.
   with some number of decimal digits stored in each word
 */

/* 
   Number of decimal digits in word.
   Must fit into uint32_t
*/
#define Q25_DIGITS 9
#define Q25_RADIX (1000*1000*1000)

/*
  Maintain working area for building digit representations.
  Have fixed number of words.  Use q25_t for meta information
  but separate extensible arrays for digits.
*/

/* Working area parameters */

/* How many numbers are in working area */
#define DCOUNT 3
/* How many digits are allocated in initial arrays */
#define INIT_DIGITS 100
/* Default ID for working area */
#define WID 0

bool initialized = false;
/* Per-number components */
static q25_t working_val[DCOUNT];
static unsigned *digit_buffer[DCOUNT];
static unsigned digit_allocated[DCOUNT];

/* 
   Static function prototypes.
   Use id to index the different numbers
*/

/* Put into canonical form */
static void q25_canonize(int id);
// Set working value to number x < RADIX
static void q25_set(int id, uint32_t x);
// Make sure enough digits in working space
static void q25_check(int id, unsigned dcount);

/* Static functions */

/* Initialize data structures */
static void q25_init() {
    if (initialized)
	return;
    initialized = true;
    int id;
    for (id = 0; id < DCOUNT; id++) {
	digit_allocated[id] = INIT_DIGITS;
	digit_buffer[id] = calloc(INIT_DIGITS, sizeof(uint32_t));
	digit_buffer[id][0] = 0;
	working_val[id].valid = true;
	working_val[id].pwr2 = 0;
	working_val[id].pwr5 = 0;
	working_val[id].dcount = 1;
    }
}

// Setting working value to number x < RADIX
static void q25_set(int id, uint32_t x) {
    q25_init();
    working_val[id].valid = true;
    working_val[id].pwr2 = 0;
    working_val[id].pwr5 = 0;
    working_val[id].dcount = 1;
    digit_buffer[id][0] = x;
    q25_canonize(id);
}

// Move value into working space
static void q25_work(int id, q25_ptr q) {
    q25_check(id, q->dcount);
    working_val[id].valid = q->valid;
    working_val[id].negative = q->negative;
    working_val[id].dcount = q->dcount;
    working_val[id].pwr2 = q->pwr2;
    working_val[id].pwr5 = q->pwr5;
    memcpy(digit_buffer, working_val[id].digit, working_val[id].dcount * sizeof(uint32_t));
}

// Make sure enough digits in working space
static void q25_check(int id, unsigned dcount) {
    q25_init();
    if (dcount <= digit_allocated[id])
	return;
    digit_allocated[id] *= 2;
    if (dcount > digit_allocated[id])
	digit_allocated[2] = dcount;
    digit_buffer[id] = realloc(digit_buffer[id], digit_allocated[id] * sizeof(uint32_t));
}

// Divide by a number < RADIX
// Assume dividend is valid and nonzero, and divisor is nonzero
// Return remainder
static uint32_t q25_div(int id, uint32_t divisor) {
    if (divisor == 1)
	return 0;
    uint64_t upper = 0;
    int d;
    for (d = working_val[id].dcount-1; d >= 0; d--) {
	uint64_t dividend = (upper * Q25_RADIX) + digit_buffer[id][d];
	digit_buffer[id][d] = dividend/divisor;
	upper = dividend % divisor;
    }
    // See if upper digit set to 0
    if (working_val[id].dcount > 1 && digit_buffer[id][working_val[id].dcount-1] == 0)
	working_val[id].dcount--;
    return upper;
}

/* Take out multiples of n, where n = 2^p2 * 5^p5, and n <= RADIX */
static void q25_reduce_multiple(int id, uint32_t p2, uint32_t p5, uint32_t n) {
    uint32_t word;
    while ((word = digit_buffer[id][0])  % n == 0) {
	int pwr = 0;
	uint64_t scale = 1;
	while (scale <= Q25_RADIX && word % (scale * n) == 0) {
	    pwr ++;
	    scale *= n;
	}
	q25_div(id, scale);
	working_val[id].pwr2 += p2*pwr;
	working_val[id].pwr5 += p5*pwr;
    }
}

/* Take out as many multiples of 10 as possible.  Assume nonzero */
static void q25_reduce10(int id) {
    // Get as many words as possible
    uint32_t wcount = 0;
    while (wcount < working_val[id].dcount && digit_buffer[id][wcount] == 0)
	wcount++;
    // Shift words down
    uint32_t idest = 0;
    uint32_t isrc = wcount;
    while (isrc < working_val[id].dcount) {
	digit_buffer[id][idest++] = digit_buffer[id][isrc++];
    }
    working_val[id].dcount -= wcount;
    working_val[id].pwr2 += Q25_DIGITS * wcount;
    working_val[id].pwr5 += Q25_DIGITS * wcount;
    // Do the final digits
    q25_reduce_multiple(id, 1, 1, 10);
}

// Take out powers of two
static void q25_reduce2(int id) {
    q25_reduce_multiple(id, 1, 0, 2);
}

// Take out powers of five
static void q25_reduce5(int id) {
    q25_reduce_multiple(id, 0, 1, 5);
}

/* Canonize working value */
static void q25_canonize(int id) {
    if (!working_val[id].valid) {
	working_val[id].negative = false;
	working_val[id].dcount = 1;
	digit_buffer[id][0] = 0;
	working_val[id].pwr2 = 0;
	working_val[id].pwr5 = 0;
    } else {
	// Make sure have the right number of digits
	while (working_val[id].dcount > 1 && digit_buffer[id][working_val[id].dcount-1] == 0)
	    working_val[id].dcount--;
	if (working_val[id].dcount == 1 && digit_buffer[id][0] == 0) {
	    working_val[id].negative = false;
	    working_val[id].pwr2 = 0;
	    working_val[id].pwr5 = 0;
	} else {
	    // Diminish by powers of 10, 2, and 5
	    q25_reduce10(id);
	    q25_reduce2(id);
	    q25_reduce5(id);
	}
    }
}

// Convert the working version into a true q25_t
static q25_ptr q25_build(int id) {
    q25_canonize(id);
    size_t len = sizeof(q25_t) + (working_val[id].dcount - 1) * sizeof(uint32_t);
    q25_ptr result = malloc(len);
    if (result == NULL)
	return NULL;
    result->valid = working_val[id].valid;
    result->negative = working_val[id].negative;
    result->dcount = working_val[id].dcount;
    result->pwr2 = working_val[id].pwr2;
    result->pwr5 = working_val[id].pwr5;
    memcpy(result->digit, working_val[id].digit, working_val[id].dcount * sizeof(uint32_t));
    return result;
}

/**** Externally visible functions ****/

void q25_free(q25_ptr q) {
    free((void *) q);
}

/* Convert int64_t to q25 form */
#define I64_DIGITS 20
q25_ptr q25_from_64(int64_t x) {
    int wcount = (I64_DIGITS + Q25_DIGITS-1)/Q25_DIGITS;
    q25_check(WID, wcount);
    q25_set(WID, 0);
    if (x == 0)
	return q25_build(WID);
    if (x < 0) {
	working_val[WID].negative = true;
	x = -x;
    }
    working_val[WID].dcount = 0;
    while (x > 0) {
	digit_buffer[WID][working_val[WID].dcount++] = x % Q25_RADIX;
	x = x / Q25_RADIX;
    }
    return q25_build(WID);
}

/* Convert int32_t to q25 form */
#define I32_DIGITS 10
q25_ptr q25_from_32(int32_t x) {
    int wcount = (I32_DIGITS + Q25_DIGITS-1)/Q25_DIGITS;
    q25_check(WID, wcount);
    q25_set(WID, 0);
    if (x == 0)
	return q25_build(WID);
    if (x < 0) {
	working_val[WID].negative = true;
	x = -x;
    }
    working_val[WID].dcount = 0;
    while (x > 0) {
	digit_buffer[WID][working_val[WID].dcount++] = x % Q25_RADIX;
	x = x / Q25_RADIX;
    }
    return q25_build(WID);
}

q25_ptr q25_scale(q25_ptr q, int32_t p2, int32_t p5) {
    q25_work(WID, q);
    working_val[WID].pwr2 += p2;
    working_val[WID].pwr5 += p5;
    return q25_build(WID);
}

q25_ptr q25_negate(q25_ptr q) {
    q25_work(WID, q);
    working_val[WID].negative = !working_val[WID].negative;
    return q25_build(WID);
}

// Can only compute reciprocal when d == 1
// Otherwise invalid
q25_ptr q25_recip(q25_ptr q) {
    q25_set(WID, 1);
    if (!q->valid || q->dcount > 1 || q->digit[0] != 1) {
	working_val[WID].valid = false;
    } else {
	working_val[WID].pwr2 = -q->pwr2;
	working_val[WID].pwr5 = -q->pwr5;
    }
    return q25_build(WID);
}

bool q25_valid(q25_ptr q) {
    return q->valid;
}

bool q25_is_zero(q25_ptr q) {
    return q->valid && q->dcount == 0 && q->digit[0] == 0;
}

bool q25_equal(q25_ptr q1, q25_ptr q2) {
    if (q1->valid != q2->valid)
	return false;
    if (q1->negative != q2->negative)
	return false;
    if (q1->dcount != q2->dcount)
	return false;
    int d;
    for (d = 0; d < q1->dcount ; d++) {
	if (q1->digit[d] != q2->digit[d])
	    return false;
    }
    return true;
}


q25_ptr q25_add(q25_ptr q1, q25_ptr q2) {
    /* Must move arguments into working area */
    q25_work(0, q1);
    q25_work(1, q2);
    return q25_build(0);
}

q25_ptr q25_mul(q25_ptr q1, q25_ptr q2) {
    if (q25_is_zero(q1) || !q1->valid)
	return q1;
    if (q25_is_zero(q2) || !q2->valid)
	return q2;
    q25_set(WID, 0);
    // Figure out sign
    working_val[WID].negative = (q1->negative != q2->negative);
    // Set powers
    working_val[WID].pwr2 = q1->pwr2 + q2->pwr2;
    working_val[WID].pwr5 = q1->pwr5 + q2->pwr5;
    // Clear out space for the product
    unsigned len = q1->dcount + q2->dcount + 1;
    q25_check(WID, len);
    memset(digit_buffer[WID], 0, len * sizeof(uint32_t));
    working_val[WID].dcount = len;
    // Make sure q1 is longer
    if (q1->dcount < q2->dcount) {
	q25_ptr qt = q1; q1 = q2; q2 = qt;
    }
    unsigned d1, d2;
    for (d2 = 0; d2 < q2->dcount; d2++) {
	uint64_t digit2 = q2->digit[d2];
	uint64_t carry = 0;
	for (d1 = 0; d1 < q1->dcount; d1++) {
	    uint64_t ndigit = q1->digit[d1] * digit2 + carry + digit_buffer[WID][d1+d2];
	    digit_buffer[WID][d1+d2] = ndigit % Q25_RADIX;
	    carry = ndigit / Q25_RADIX;
	}
	digit_buffer[WID][d1+d2] = carry;
    }
    return q25_build(WID);
}

q25_ptr q25_read(FILE *infile) {
    q25_set(WID, 0);
    return q25_build(WID);
}

void q25_write(q25_ptr q, FILE *outfile) {
    q25_work(WID, q);
}
