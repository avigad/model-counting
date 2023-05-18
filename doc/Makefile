INTERP=python3
DGEN = $(INTERP) ../tools/gen-data.py
LDATA = ../benchmarks/mc2022/logs
SRCDATA = data-raw

all:
	cd dd ; make
	cd ../benchmarks/mc2022/logs ; make data
	make rdata
	make pdata
	pdflatex mc-paper
	bibtex mc-paper
	pdflatex mc-paper	
	pdflatex mc-paper

rdata:
	rm -rf $(SRCDATA)
	mkdir $(SRCDATA)
	cp -p $(LDATA)/time+defining.csv $(SRCDATA)
	cp -p $(LDATA)/time+defining-success.csv $(SRCDATA)
	cp -p $(LDATA)/time+defining-onesided-only.csv $(SRCDATA)
	cp -p $(LDATA)/time+defining-failure.csv $(SRCDATA)
	cp -p $(LDATA)/time-d4-verify.csv $(SRCDATA)
	cp -p $(LDATA)/time-d4-verify-onesided-only.csv $(SRCDATA)
	cp -p $(LDATA)/time-d4-failure.csv $(SRCDATA)
	cp -p $(LDATA)/defining+total.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-defining-onesided.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-defining-failure.csv $(SRCDATA)
	cp -p $(LDATA)/times.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-lemma-nolemma.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-nosplit-split.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-optimized-unoptimized.csv $(SRCDATA)
	cp -p $(LDATA)/time-mice-compare.csv $(SRCDATA)
#	cp -p $(LDATA)/time-mice-error.csv $(SRCDATA)
	cp -p $(LDATA)/time-mice-timeout.csv $(SRCDATA)
	cp -p $(LDATA)/time-structured+monolithic.csv $(SRCDATA)
	cp -p $(LDATA)/time-structured+monolithic_timeout.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-total-structured+monolithic.csv $(SRCDATA)
	cp -p $(LDATA)/time-check-regular-lean.csv $(SRCDATA)
	cp -p $(LDATA)/time-monolithic+preprocess.csv $(SRCDATA)
	cp -p $(LDATA)/clauses-total-monolithic+preprocess.csv $(SRCDATA)
	cp -p $(LDATA)/time-toolchain-compare-cd4-timeout.csv $(SRCDATA)
	cp -p $(LDATA)/time-toolchain-compare-pog-fail.csv $(SRCDATA)	
	cp -p $(LDATA)/time-toolchain-compare.csv $(SRCDATA)	


pdata:
	rm -rf data-formatted
	mkdir data-formatted
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time+defining-success.csv > data-formatted/time+defining-success.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=bluegray, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time+defining-onesided-only.csv > data-formatted/time+defining-onesided-only.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/time+defining-failure.csv > data-formatted/time+defining-failure.tex
	$(DGEN) -X 2 -Y 5 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-d4-verify.csv > data-formatted/time-d4-verify.tex
	$(DGEN) -x 3000000000 -X 2 -y 5000000000 -Y 5 -O "only marks, color=bluegray, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-defining-onesided.csv > data-formatted/clauses-defining-onesided.tex
	$(DGEN) -x 3000000000 -X 2 -y 5000000000 -Y 4 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/clauses-defining-failure.csv > data-formatted/clauses-defining-failure.tex
#	$(DGEN) -X 2 -Y 5 -O "only marks, color=bluegray, mark=square*,  mark options={scale=0.8}, opacity=0.7" \
#		< $(SRCDATA)/time-d4-verify-onesided.csv > data-formatted/time-d4-verify-onesided.tex
	$(DGEN) -X 2 -Y 6 -O "only marks, color=bluegray, mark=square*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-d4-verify-onesided-only.csv > data-formatted/time-d4-verify-onesided-only.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
	 	< $(SRCDATA)/time-d4-failure.csv > data-formatted/time-d4-failure.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/defining+total.csv > data-formatted/defining+total.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redpurple, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-lemma-nolemma.csv > data-formatted/clauses-lemma-nolemma.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=medgreen, mark=diamond*,  mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/clauses-nosplit-split.csv > data-formatted/clauses-nosplit-split.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=darkestblue, mark=pentagon*,  mark options={scale=0.8}, opacity=0.8" \
		< $(SRCDATA)/clauses-optimized-unoptimized.csv > data-formatted/clauses-optimized-unoptimized.tex
	$(DGEN) -X 4 -Y 7 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-mice-compare.csv > data-formatted/time-mice-compare.tex
	$(DGEN) -X 5 -Y 6 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-mice-timeout.csv > data-formatted/time-mice-timeout.tex
	$(DGEN) -X 4 -Y 7 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-structured+monolithic.csv > data-formatted/time-structured+monolithic.tex
	$(DGEN) -X 4 -Y 6 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-structured+monolithic_timeout.csv > data-formatted/time-structured+monolithic_timeout.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-total-structured+monolithic.csv > data-formatted/clauses-total-structured+monolithic.tex
	$(DGEN) -X 5 -Y 9 -x 1000 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-monolithic+preprocess.csv > data-formatted/time-monolithic+preprocess.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-total-monolithic+preprocess.csv > data-formatted/clauses-total-monolithic+preprocess.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-check-regular-lean.csv > data-formatted/time-check-regular.tex
	$(DGEN) -X 2 -Y 4 -O "only marks, color=bluegray, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-check-regular-lean.csv > data-formatted/time-check-lean.tex
	$(DGEN) -X 5 -Y 7 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-toolchain-compare-cd4-timeout.csv > data-formatted/time-toolchain-compare-cd4-timeout.tex
	$(DGEN) -X 3 -Y 7 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-toolchain-compare-pog-fail.csv > data-formatted/time-toolchain-compare-pog-fail.tex
	$(DGEN) -X 5 -Y 9 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-toolchain-compare.csv > data-formatted/time-toolchain-compare.tex
