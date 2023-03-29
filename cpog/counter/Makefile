CC=gcc
CFLAGS=-O0 -g -Wno-nullability-completeness

q25.o: q25.c q25.h
	$(CC) $(CFLAGS) -c q25.c

q25_rpn: q25.o q25_rpn.c
	$(CC) $(CFLAGS) -o q25_rpn q25.o q25_rpn.c

clean:
	rm -f *~ *.o
	rm -f q25_rpn
	rm -rf *.dSYM

