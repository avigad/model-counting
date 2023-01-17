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

clausal.o: ilist.h clausal.hh writer.hh clausal.cpp
	$(CXX) $(CPPFLAGS) -c clausal.cpp

writer.o: ilist.h report.h writer.hh writer.cpp
	$(CXX) $(CPPFLAGS) -c writer.cpp

pog.o: pog.hh clausal.hh pog.cpp
	$(CXX) $(CPPFLAGS) -c pog.cpp

brun: brun.cpp clausal.o ilist.o report.o writer.o
	$(CXX) $(CPPFLAGS) -o brun brun.cpp clausal.o ilist.o report.o writer.o

rrun: rrun.cpp clausal.o ilist.o report.o writer.o
	$(CXX) $(CPPFLAGS) -o rrun rrun.cpp clausal.o ilist.o report.o writer.o

d2p: d2p.cpp clausal.o ilist.o report.o writer.o pog.o

.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -c $<

clean:
	rm -f *.o *~
	rm -f brun rrun


