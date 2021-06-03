This directory contains a program that converts the CNF representation
of a Boolean formula into a model-preserving BDD.  It generates the BDD as both
an ITEG and as a set of clauses.

The input is based on the QDIMACS format
(http://www.qbflib.org/qdimacs.html), allowing existential
quantification with the "e" directive.  All variables that are not
part of an existential block are considered to be free.

The program optionally generates a clausal proof showing that the
generated output clauses are logically equivalent to the input CNF.
