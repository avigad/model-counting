CC=gcc
CXX=g++
#OPT=-O2
OPT=-O0
CFLAGS=-g $(OPT) -Wno-nullability-completeness
CPPFLAGS=-g $(OPT) -Wno-nullability-completeness -std=c++11

all:  pkc

report.o: report.c report.h
	$(CC) $(CFLAGS) -c report.c

ilist.o: ilist.c ilist.h
	$(CC) $(CFLAGS) -c ilist.c

counters.o: counters.c counters.h
	$(CC) $(CFLAGS) -c counters.c

clause.o: report.h counters.h clause.hh clause.cpp
	$(CXX) $(CPPFLAGS) -c clause.cpp

pog.o: pog.hh clause.hh counters.h pog.cpp
	$(CXX) $(CPPFLAGS) -c pog.cpp

pkc: pkc.cpp clause.o report.o counters.o ilist.o
	$(CXX) $(CPPFLAGS) -o pkc pkc.cpp clause.o report.o counters.o ilist.o

pog_test: pog_test.cpp clause.o report.o counters.o ilist.o pog.o
	$(CXX) $(CPPFLAGS) -o pog_test pog_test.cpp clause.o report.o counters.o ilist.o pog.o

.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -c $<

clean:
	rm -f *.o *~
	rm -f pkc



