CC=gcc
CXX=g++
OPT=-O2
#OPT=-O0
CFLAGS=-g $(OPT) -Wno-nullability-completeness
CPPFLAGS=-g $(OPT) -Wno-nullability-completeness -std=c++11

all:  cpog-generate dcpog-generate

ilist.o: ilist.c ilist.h
	$(CC) $(CFLAGS) -c ilist.c

report.o: report.c report.h
	$(CC) $(CFLAGS) -c report.c

counters.o: counters.c counters.h
	$(CC) $(CFLAGS) -c counters.c

clausal.o: ilist.h counters.h clausal.hh writer.hh clausal.cpp
	$(CXX) $(CPPFLAGS) -c clausal.cpp

writer.o: ilist.h report.h writer.hh writer.cpp
	$(CXX) $(CPPFLAGS) -c writer.cpp

pog.o: pog.hh clausal.hh counters.h pog.cpp
	$(CXX) $(CPPFLAGS) -c pog.cpp

cpog-generate: cpog-generate.cpp clausal.o ilist.o report.o counters.o writer.o pog.o
	$(CXX) $(CPPFLAGS) -o cpog-generate cpog-generate.cpp clausal.o ilist.o report.o counters.o writer.o pog.o

clausal.do: ilist.h counters.h clausal.hh writer.hh clausal.cpp
	$(CXX) $(CPPFLAGS) -DDEBUG -c clausal.cpp -o clausal.do

pog.do: pog.hh clausal.hh counters.h pog.cpp
	$(CXX) $(CPPFLAGS) -DDEBUG -c pog.cpp -o pog.do

dcpog-generate: cpog-generate.cpp clausal.do ilist.o report.o counters.o writer.o pog.do
	$(CXX) $(CPPFLAGS) -o dcpog-generate cpog-generate.cpp clausal.do ilist.o report.o counters.o writer.o pog.do


brun: brun.cpp clausal.o ilist.o report.o writer.o counters.o
	$(CXX) $(CPPFLAGS) -o brun brun.cpp clausal.o ilist.o report.o writer.o counters.o

rrun: rrun.cpp clausal.o ilist.o report.o writer.o  counters.o
	$(CXX) $(CPPFLAGS) -o rrun rrun.cpp clausal.o ilist.o report.o writer.o  counters.o



.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -c $<

clean:
	rm -f *.o *~
	rm -f brun rrun cpog-generate dcpog-generate


