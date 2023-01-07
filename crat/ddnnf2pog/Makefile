CC=gcc
CXX=g++
#OPT=-O2
OPT=-O0
CFLAGS=-g $(OPT) -Wno-nullability-completeness
CPPFLAGS=-g $(OPT) -Wno-nullability-completeness -std=c++11

ilist.o: ilist.c ilist.h
	$(CC) $(CFLAGS) -c ilist.c

report.o: report.c report.h
	$(CC) $(CFLAGS) -c report.c

clause.o: ilist.h clause.hh clause.cpp
	$(CXX) $(CPPFLAGS) -c clause.cpp

brun: brun.cpp clause.o ilist.o report.o
	$(CXX) $(CPPFLAGS) -o brun brun.cpp clause.o ilist.o report.o


.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -c $<

clean:
	rm -f *.o *~
	rm -f brun


