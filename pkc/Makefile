CC=gcc
CXX=g++
#OPT=-O2
OPT=-O0
CFLAGS=-g $(OPT) -Wno-nullability-completeness
CPPFLAGS=-g $(OPT) -Wno-nullability-completeness -std=c++11

all:  pkc

report.o: report.c report.h
	$(CC) $(CFLAGS) -c report.c

counters.o: counters.c counters.h
	$(CC) $(CFLAGS) -c counters.c

q25.o: q25.c q25.h
	$(CC) $(CFLAGS) -c q25.c

clause.o: report.h counters.h clause.hh clause.cpp
	$(CXX) $(CPPFLAGS) -c clause.cpp

pog.o: pog.hh clause.hh counters.h pog.cpp
	$(CXX) $(CPPFLAGS) -c pog.cpp

project.o: project.hh clause.hh pog.hh project.cpp
	$(CXX) $(CPPFLAGS) -c project.cpp

pkc: pkc.cpp clause.o report.o counters.o pog.o project.o q25.o
	$(CXX) $(CPPFLAGS) -o pkc pkc.cpp clause.o report.o counters.o pog.o project.o q25.o

.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -c $<

clean:
	rm -f *.o *~
	rm -f pkc



