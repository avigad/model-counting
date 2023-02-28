INTERP=python3
DGEN = $(INTERP) ../tools/gen-data.py
LDATA = ../benchmarks/mc2022/logs
SRCDATA = data-raw



rdata:
	cp -p $(LDATA)/time+defining.csv $(SRCDATA)
	cp -p $(LDATA)/time+defining-success.csv $(SRCDATA)
	cp -p $(LDATA)/time+defining-failure.csv $(SRCDATA)
	cp -p $(LDATA)/time-d4-verify.csv $(SRCDATA)
	cp -p $(LDATA)/defining+total.csv $(SRCDATA)
	cp -p $(LDATA)/times.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-lemma-nolemma.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-nosplit-split.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-optimized-unoptimized.csv $(SRCDATA)

data:
	rm -rf data-formatted
	mkdir data-formatted
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*, mark options={scale=0.9}, opacity=0.7" \
		< $(SRCDATA)/time+defining.csv > data-formatted/time+defining.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*, mark options={scale=0.9}, opacity=0.7" \
		< $(SRCDATA)/time+defining-success.csv > data-formatted/time+defining-success.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=darkturquoise, mark=diamond*, mark options={scale=1.0}, opacity=0.7" \
		< $(SRCDATA)/time+defining-failure.csv > data-formatted/time+defining-failure.tex
	$(DGEN) -X 2 -Y 5 -O "only marks, color=redorange, mark=*,  mark options={scale=0.9}, opacity=0.7" \
		< $(SRCDATA)/time-d4-verify.csv > data-formatted/time-d4-verify.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*,  mark options={scale=0.9}, opacity=0.7" \
		< $(SRCDATA)/defining+total.csv > data-formatted/defining+total.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redpurple, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-lemma-nolemma.csv > data-formatted/clauses-lemma-nolemma.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=medgreen, mark=diamond*,  mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/clauses-nosplit-split.csv > data-formatted/clauses-nosplit-split.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=darkestblue, mark=pentagon*,  mark options={scale=0.9}, opacity=0.8" \
		< $(SRCDATA)/clauses-optimized-unoptimized.csv > data-formatted/clauses-optimized-unoptimized.tex
