CC=gcc
CFLAGS=-O3 -g -Wno-nullability-completeness

check: cpog-check

q25.o: q25.c q25.h
	$(CC) $(CFLAGS) -c q25.c

cpog-check: cpog-check.c q25.o
	$(CC) $(CFLAGS) cpog-check.c q25.o -o cpog-check

q25_rpn: q25_rpn.c q25.o
	$(CC) $(CFLAGS) -o q25_rpn q25_rpn.c q25.o

clean:
	rm -f *~
	rm -f *.o
	rm -rf *.dSYM
	rm -f cpog_check q25_rpn
