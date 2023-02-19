INTERP=python3
DGEN = $(INTERP) ../tools/gen-data.py
LDATA = ../benchmarks/mc2022/logs
SRCDATA = data-raw



rdata:
	cp -p $(LDATA)/time+defining.csv $(SRCDATA)
	cp -p $(LDATA)/time-d4-gen.csv $(SRCDATA)
	cp -p $(LDATA)/defining+total.csv $(SRCDATA)
	cp -p $(LDATA)/times.csv $(SRCDATA)

data:
	rm -rf data-formatted
	mkdir data-formatted
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=pentagon*, thick" < $(SRCDATA)/time+defining.csv > data-formatted/time+defining.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=pentagon*, thick" < $(SRCDATA)/time-d4-gen.csv > data-formatted/time-d4-gen.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redpurple, mark=diamond*, thick" < $(SRCDATA)/defining+total.csv > data-formatted/defining+total.tex
