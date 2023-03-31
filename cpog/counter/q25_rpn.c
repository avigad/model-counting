/* Simple RPN calculator for Q25 values */

/* 
   Unary operators:
   ~ Negation
   ! Factorial
   / Reciprocal
   f Power of 5
   t Power of 2
   : Compare.  Returns -1 (less), 0 (equal), or 1 (greater)

   Binary operators:
   + Addition
   * Multiplication


 */

#include "q25.h"
#include <stdlib.h>
#include <ctype.h>

int verblevel = 1;

void usage(char *name) {
    printf("Usage: %s [-h] [-v VERB]\n", name);
    printf(" -h           Print this message\n");
    printf(" -v VERB      Set verbosity level\n");
    exit(0);
}

void show_result(q25_ptr q, char *opname) {
    if (verblevel >= 3) {
	printf("  %s result representation: ", opname);
	q25_show(q, stdout);
	printf("\n");
	printf("    --> ");
	q25_write(q, stdout);
	printf("\n");
	    
    } else if (verblevel >= 2) {
	printf("  %s: ", opname);
	q25_write(q, stdout);
	printf("\n");
    }
}

q25_ptr do_negate(q25_ptr q) {
    q25_ptr result = q25_negate(q);
    show_result(result, "Negation");
    return result;
}

q25_ptr do_power2(q25_ptr q) {
    int64_t pwr;
    bool ok = get_int64(q, &pwr);
    if (!ok) {
	if (verblevel >= 1) {
	    printf("WARNING: Could not extract integer from representation ");
	    q25_show(q, stdout);
	    printf("\n");
	}
	return q25_invalid();
    }
    int ipwr = (int) pwr;
    if (verblevel >= 3) {
	printf("  Extracted integer power %d from representation ", ipwr);
	q25_show(q, stdout);
	printf("\n");
    }
    q25_ptr one = q25_from_32(1);
    q25_ptr result = q25_scale(one, ipwr, 0);
    q25_free(one);
    show_result(result, "Power 2 scale");
    return result;
}

q25_ptr do_power5(q25_ptr q) {
    int64_t pwr;
    bool ok = get_int64(q, &pwr);
    if (!ok) {
	if (verblevel >= 1) {
	    printf("WARNING: Could not extract integer from representation ");
	    q25_show(q, stdout);
	    printf("\n");
	}
	return q25_invalid();
    }
    int ipwr = pwr;
    if (verblevel >= 3) {
	printf("  Extracted integer power %d from representation ", ipwr);
	q25_show(q, stdout);
	printf("\n");
    }
    q25_ptr one = q25_from_32(1);
    q25_ptr result = q25_scale(one, 0, ipwr);
    q25_free(one);
    show_result(result, "Power 5 scale");
    return result;
}

q25_ptr do_factorial(q25_ptr q) {
    int64_t n;
    bool ok = get_int64(q, &n);
    if (!ok) {
	if (verblevel >= 1) {
	    printf("WARNING: Could not extract integer from representation ");
	    q25_show(q, stdout);
	    printf("\n");
	}
	return q25_invalid();
    }
    int in = (int) n;
    if (verblevel >= 3) {
	printf("  Extracted integer %d from representation ", in);
	q25_show(q, stdout);
	printf("\n");
    }
    q25_ptr fact = q25_from_32(1);
    int i;
    for (i = 2; i <= in; i++) {
	q25_ptr qi = q25_from_32(i);
	q25_ptr nfact = q25_mul(fact, qi);
	q25_free(qi);
	q25_free(fact);
	fact = nfact;
    }
    show_result(fact, "Factorial");
    return fact;
}


q25_ptr do_reciprocal(q25_ptr q) {
    q25_ptr result = q25_recip(q);
    show_result(result, "Reciprocal");
    return result;
}


q25_ptr do_multiply(q25_ptr q1, q25_ptr q2) {
    q25_ptr result = q25_mul(q1, q2);
    show_result(result, "Multiplication");
    return result;
}

q25_ptr do_add(q25_ptr q1, q25_ptr q2) {
    q25_ptr result = q25_add(q1, q2);
    show_result(result, "Addition");
    return result;
}

q25_ptr do_compare(q25_ptr q1, q25_ptr q2) {
    int comp = q25_compare(q1, q2);
    q25_ptr result = q25_from_32((int32_t) comp);
    show_result(result, "Comparison");
    return result;
}

q25_ptr result_stack[1000];
int stack_count = 0;

/* 
   Unary operators:
   -: Negation
   !: Factorial
   /: Reciprocal
   f: Power of 5
   t: Power of 2
   F: Fibonacci

   Binary operators:
   +: Addition
   *: Multiplication
   B: Binomial coefficient

 */


bool stack_ok(int cnt) {
    if (stack_count < cnt) {
	printf("ERROR.  Only %d elements on stack.  Need %d\n", stack_count, cnt);
	return false;
    }
    return true;
}

bool do_line() {
    int c;
    q25_ptr q, q1, q2;
    while ((c = getchar()) != EOF) {
	if (isdigit(c) || c == '-') {
	    ungetc(c, stdin);
	    q = q25_read(stdin);
	    if (!q25_valid(q)) {
		printf("Error.  Could not read number starting with digit %c\n", c);
		return false;
	    }
	    result_stack[stack_count++] = q;
	    continue;
	}
	switch (c) {
	case '\n':
	    {
		bool ok = stack_count == 1;
		if (ok) {
		    if (verblevel >= 2) {
			printf("Result respresentation: ");
			q25_show(result_stack[0], stdout);
			printf("\n  --> ");
			q25_write(result_stack[0], stdout);
			printf("\n");

		    } else {
			printf("Result = ");
			q25_write(result_stack[0], stdout);
			printf("\n");
		    }
		} else
		    printf("ERROR.  Line completed with %d elements on stack\n", stack_count);
		int i;
		for (i = 0; i < stack_count; i++)
		    q25_free(result_stack[i]);
		stack_count = 0;
		return ok;
	    }
	case ' ':
	    break;
	case '~':
	    if (!stack_ok(1))
		return false;
	    q1 = result_stack[--stack_count];
	    q = do_negate(q1);
	    result_stack[stack_count++] = q;
	    break;
	case 'f':
	    if (!stack_ok(1))
		return false;
	    q1 = result_stack[--stack_count];
	    q = do_power5(q1);
	    result_stack[stack_count++] = q;
	    break;
	case 't':
	    if (!stack_ok(1))
		return false;
	    q1 = result_stack[--stack_count];
	    q = do_power2(q1);
	    result_stack[stack_count++] = q;
	    break;
	case '/':
	    if (!stack_ok(1))
		return false;
	    q1 = result_stack[--stack_count];
	    q = do_reciprocal(q1);
	    result_stack[stack_count++] = q;
	    break;
	case '!':
	    if (!stack_ok(1))
		return false;
	    q1 = result_stack[--stack_count];
	    q = do_factorial(q1);
	    result_stack[stack_count++] = q;
	    break;
	case ':':
	    if (!stack_ok(2))
		return false;
	    q2 = result_stack[--stack_count];
	    q1 = result_stack[--stack_count];
	    q = do_compare(q1, q2);
	    result_stack[stack_count++] = q;
	    break;
	case '+':
	    if (!stack_ok(2))
		return false;
	    q2 = result_stack[--stack_count];
	    q1 = result_stack[--stack_count];
	    q = do_add(q1, q2);
	    result_stack[stack_count++] = q;
	    break;
	case '*':
	    if (!stack_ok(2))
		return false;
	    q2 = result_stack[--stack_count];
	    q1 = result_stack[--stack_count];
	    q = do_multiply(q1, q2);
	    result_stack[stack_count++] = q;
	    break;
	default:
	    printf("Uknown operator '%c'\n", c);
	    return false;
	}
    }
    return false;
}

int main(int argc, char *argv[]) {
    verblevel = 1;
    int argi;
    char *istring;
    for (argi = 1; argi < argc; argi++) {
	if (argv[argi][0] != '-') {
	    usage(argv[0]);
	    exit(0);
	}
	switch(argv[argi][1]) {
	case 'h':
	    usage(argv[0]);
	    exit(0);
	case 'v':
	    istring = argv[++argi];
	    verblevel = atoi(istring);
	    printf("Setting verblevel to %d\n", verblevel);
	    break;
	default:
	    printf("Unknown command line option %s\n", argv[argi]);
	    usage(argv[0]);
	    exit(1);
	}
    }
    while (do_line())
	;
    return 0;
}
