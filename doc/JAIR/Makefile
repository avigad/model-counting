INTERP=python3
DGEN = $(INTERP) ../../tools/gen-data.py
LDATA = ../../benchmarks/mc2022-v2/logs
SRCDATA = data-raw

all:
	cd dd ; make
	cd ../benchmarks/mc2022-v2/logs ; make data
	make rdata
	make pdata

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

	# Mono
	cp -p $(LDATA)/sub10M-seconds-mono.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-seconds-failures-mono.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-mono.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-failures-mono.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-toobig-mono.csv $(SRCDATA)
	# Structured
	cp -p $(LDATA)/sub10M-seconds-structured.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-seconds-failures-structured.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-structured.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-failures-structured.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-toobig-structured.csv $(SRCDATA)
	# Hybrid
	cp -p $(LDATA)/sub10M-seconds-hybrid.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-seconds-failures-hybrid.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-hybrid.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-failures-hybrid.csv $(SRCDATA)
	cp -p $(LDATA)/sub10M-clauses-toobig-hybrid.csv $(SRCDATA)


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
	$(DGEN) -x 2500000000 -y 2500000000 -X 2 -Y 3 -O "only marks, color=redorange, mark=*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary.csv > data-formatted/clauses-summary.tex
	$(DGEN) -x 2500000000 -y 2500000000 -X 2 -Y 3 -O "only marks, color=browngreen, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary-structured-only.csv > data-formatted/clauses-summary-structured-only.tex
	$(DGEN) -x 2500000000 -y 2500000000 -X 3 -Y 4 -O "only marks, color=bluegray, mark=triangle*, mark options={scale=1.2}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary-onesided.csv > data-formatted/clauses-summary-onesided.tex
	$(DGEN) -x 2500000000 -y 2500000000 -X 3 -Y 4 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/clauses-summary-failures.csv > data-formatted/clauses-summary-failures.tex
	# Mono
	$(DGEN) -X 2 -Y 6 -O "only marks, color=redorange, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-mono.csv > data-formatted/sub10M-seconds-mono.tex
	$(DGEN) -X 2 -Y 4 -O "only marks, color=redorange, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-failures-mono.csv > data-formatted/sub10M-seconds-failures-mono.tex
	$(DGEN) -X 7 -Y 8 -O "only marks, color=redorange, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-mono.csv > data-formatted/sub10M-clauses-mono.tex
	$(DGEN) -X 3 -Y 4 -O "only marks, color=redorange, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-failures-mono.csv > data-formatted/sub10M-clauses-failures-mono.tex
	$(DGEN) -X 7 -Y 8 -O "only marks, color=redorange, mark=square*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-toobig-mono.csv > data-formatted/sub10M-clauses-toobig-mono.tex
	# Structured
	$(DGEN) -X 2 -Y 6 -O "only marks, color=bluegray, mark=+, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-structured.csv > data-formatted/sub10M-seconds-structured.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=bluegray, mark=+, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-failures-structured.csv > data-formatted/sub10M-seconds-failures-structured.tex
	$(DGEN) -X 7 -Y 8 -O "only marks, color=bluegray, mark=+, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-structured.csv > data-formatted/sub10M-clauses-structured.tex
	$(DGEN) -X 3 -Y 4 -O "only marks, color=bluegray, mark=+, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-failures-structured.csv > data-formatted/sub10M-clauses-failures-structured.tex
	$(DGEN) -X 7 -Y 8 -O "only marks, color=bluegray, mark=+, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-toobig-structured.csv > data-formatted/sub10M-clauses-toobig-structured.tex
	# Hybrid
	$(DGEN) -X 2 -Y 6 -O "only marks, color=darkgreen, mark=o, mark options={scale=1.5}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-hybrid.csv > data-formatted/sub10M-seconds-hybrid.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=darkgreen, mark=o, mark options={scale=1.5}, opacity=0.7" \
		< $(SRCDATA)/sub10M-seconds-failures-hybrid.csv > data-formatted/sub10M-seconds-failures-hybrid.tex
	$(DGEN) -X 7 -Y 8 -O "only marks, color=darkgreen, mark=o, mark options={scale=1.5}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-hybrid.csv > data-formatted/sub10M-clauses-hybrid.tex
	$(DGEN) -X 3 -Y 4 -O "only marks, color=darkgreen, mark=o, mark options={scale=1.5}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-failures-hybrid.csv > data-formatted/sub10M-clauses-failures-hybrid.tex
	$(DGEN) -X 7 -Y 8 -O "only marks, color=darkgreen, mark=o, mark options={scale=1.5}, opacity=0.7" \
		< $(SRCDATA)/sub10M-clauses-toobig-hybrid.csv > data-formatted/sub10M-clauses-toobig-hybrid.tex



xdata:
	$(DGEN) -X 2 -Y 3 -O "only marks, color=bluegray, mark=triangle*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time+defining-onesided-only.csv > data-formatted/time+defining-onesided-only.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/time+defining-failure.csv > data-formatted/time+defining-failure.tex
	$(DGEN) -X 2 -Y 5 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-d4-verify.csv > data-formatted/time-d4-verify.tex
	$(DGEN) -x 3000000000 -X 2 -y 5000000000 -Y 5 -O "only marks, color=bluegray, mark=triangle*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/clauses-defining-onesided.csv > data-formatted/clauses-defining-onesided.tex
	$(DGEN) -x 3000000000 -X 2 -y 5000000000 -Y 4 -O "only marks, color=darkgreen, mark=diamond*, mark options={scale=1.1}, opacity=0.7" \
		< $(SRCDATA)/clauses-defining-failure.csv > data-formatted/clauses-defining-failure.tex
#	$(DGEN) -X 2 -Y 5 -O "only marks, color=bluegray, mark=triangle*,  mark options={scale=0.8}, opacity=0.7" \
#		< $(SRCDATA)/time-d4-verify-onesided.csv > data-formatted/time-d4-verify-onesided.tex
	$(DGEN) -X 2 -Y 6 -O "only marks, color=bluegray, mark=triangle*,  mark options={scale=0.8}, opacity=0.7" \
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
	$(DGEN) -X 2 -Y 4 -O "only marks, color=bluegray, mark=triangle*, mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-check-regular-lean.csv > data-formatted/time-check-lean.tex
	$(DGEN) -X 5 -Y 7 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-toolchain-compare-cd4-timeout.csv > data-formatted/time-toolchain-compare-cd4-timeout.tex
	$(DGEN) -X 3 -Y 7 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-toolchain-compare-pog-fail.csv > data-formatted/time-toolchain-compare-pog-fail.tex
	$(DGEN) -X 5 -Y 9 -O "only marks, color=redorange, mark=*,  mark options={scale=0.8}, opacity=0.7" \
		< $(SRCDATA)/time-toolchain-compare.csv > data-formatted/time-toolchain-compare.tex
