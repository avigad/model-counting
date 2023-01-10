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

clause.o: ilist.h clause.hh writer.hh clause.cpp
	$(CXX) $(CPPFLAGS) -c clause.cpp

writer.o: ilist.h report.h writer.hh writer.cpp
	$(CXX) $(CPPFLAGS) -c writer.cpp

compressor.o: compressor.hh compressor.cpp
	$(CXX) $(CPPFLAGS) -c compressor.cpp

pog.o: pog.hh clause.hh pog.cpp compressor.hh
	$(CXX) $(CPPFLAGS) -c pog.cpp



brun: brun.cpp clause.o ilist.o report.o writer.o
	$(CXX) $(CPPFLAGS) -o brun brun.cpp clause.o ilist.o report.o writer.o

rrun: rrun.cpp clause.o ilist.o report.o writer.o
	$(CXX) $(CPPFLAGS) -o rrun rrun.cpp clause.o ilist.o report.o writer.o



.SUFFIXES: .c .cpp .o

.c.o:
	$(CC) $(CFLAGS) $(INC) -c $<

.cpp.o:
	$(CXX) $(CPPFLAGS) $(INC) -c $<

clean:
	rm -f *.o *~
	rm -f brun rrun


