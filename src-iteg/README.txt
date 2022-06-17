This directory contains a program that converts the QCNF
representation of a Boolean formula into a model-preserving BDD.  It
generates the BDD as both an ITEG and as a set of clauses.

The input is based on the QDIMACS format
(http://www.qbflib.org/qdimacs.html), allowing existential
quantification with the "e" directive.  All variables that are not
part of an existential block are considered to be free.  The generated
BDD is over those free variables.

The program generates a clausal proof showing that the generated
output clauses are logically equivalent to the input QCNF.

When specifying a nondefault ordering of the BDD variables, it is best
to have the free variables be numbered consecutively, starting at 1.
The quantified variables can occur anywhere in the ordering but should
have higher numbers.

Assuming the above convention on input variable ordering is followed,
the generated QCNF file will be canonical: two logically equivalent
input formulas will generate syntactically identical QCNF
representations.
