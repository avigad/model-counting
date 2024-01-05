INTERP=python3
DGEN = $(INTERP) ../../tools/gen-data.py
LDATA = ../../benchmarks/mc2022-v2/logs
SRCDATA = data-raw

all:
	cd dd ; make
	cd ../../benchmarks/mc2022-v2/logs ; make data
	make rdata
	make pdata
	pdflatex jair-paper
	bibtex jair-paper
	pdflatex jair-paper
	pdflatex jair-paper
	pdflatex jair-paper

rdata:
	rm -rf $(SRCDATA)
	mkdir $(SRCDATA)
# Summary
	cp -p $(LDATA)/seconds-summary.csv $(SRCDATA)
	cp -p $(LDATA)/seconds-summary-failures.csv $(SRCDATA)
	cp -p $(LDATA)/seconds-summary-onesided.csv $(SRCDATA)
	cp -p $(LDATA)/seconds-summary-structured-only.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-summary.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-summary-failures.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-summary-onesided.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-summary-structured-only.csv $(SRCDATA)
# Comparison	
	cp -p $(LDATA)/sub10M-seconds-subthresh.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-seconds-supthresh.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-subthresh.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-supthresh.csv $(SRCDATA)

pdata:
	rm -rf data-formatted
	mkdir data-formatted
# Summary	
	$(DGEN) -X 2 -Y 5 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/seconds-summary.csv > data-formatted/seconds-summary.tex
	$(DGEN) -X 2 -Y 5 -O "only marks, color=browngreen, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/seconds-summary-structured-only.csv > data-formatted/seconds-summary-structured-only.tex
	$(DGEN) -X 2 -Y 5 -O "only marks, color=bluegray, mark=triangle*, mark options={scale=1.2}, opacity=0.7" \
		< $(SRCDATA)/seconds-summary-onesided.csv > data-formatted/seconds-summary-onesided.tex
	$(DGEN) -X 3 -Y 4 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/seconds-summary-failures.csv > data-formatted/seconds-summary-failures.tex
	$(DGEN) -x 2800000000 -y 2800000000 -X 2 -Y 3 -O "only marks, color=redorange, mark=*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary.csv > data-formatted/clauses-summary.tex
	$(DGEN) -x 2800000000 -y 2800000000 -X 2 -Y 3 -O "only marks, color=browngreen, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary-structured-only.csv > data-formatted/clauses-summary-structured-only.tex
	$(DGEN) -x 2800000000 -y 2800000000 -X 3 -Y 4 -O "only marks, color=bluegray, mark=triangle*, mark options={scale=1.2}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary-onesided.csv > data-formatted/clauses-summary-onesided.tex
	$(DGEN) -x 2800000000 -y 2800000000 -X 3 -Y 4 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary-failures.csv > data-formatted/clauses-summary-failures.tex
# Compare Mono vs. Structural
	$(DGEN) -X 3 -Y 4 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-subthresh.csv > data-formatted/sub10M-seconds-subthresh.tex
	$(DGEN) -X 3 -Y 4 -O "only marks, color=bluegray, mark=square*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-supthresh.csv > data-formatted/sub10M-seconds-supthresh.tex
	$(DGEN) -X 3 -Y 4 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-subthresh.csv > data-formatted/sub10M-clauses-subthresh.tex
	$(DGEN) -X 3 -Y 4 -O "only marks, color=bluegray, mark=square*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-supthresh.csv > data-formatted/sub10M-clauses-supthresh.tex

