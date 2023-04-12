INTERP = python3
TDIR = ../../../tools
GRAB = $(TDIR)/grab_data.py
MERGE = $(TDIR)/merge_csv.py

data:
	$(INTERP) $(GRAB) "D4 LOG: Elapsed" *.D4_log > seconds-d4.csv
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.log > seconds-gen.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.log > seconds-check.csv
	$(INTERP) $(GRAB) "COUNT LOG: Elapsed" *.log > seconds-count.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.log > failures-total.csv
	$(INTERP) $(GRAB) -1 "Compressed POG has" *.D4_log > clauses-defining.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.log > clauses-total.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.nolemma_log > clauses-total-nolemma.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.split_log > clauses-total-split.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.split_nolemma_log > clauses-total-split+nolemma.csv

	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.onesided_log > seconds-gen-onesided.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.onesided_log > seconds-check-onesided.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.onesided_log > failures.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.onesided_log > clauses-total-onesided.csv


	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv > time+defining.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv clauses-total.csv > time+defining-success.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv clauses-total-onesided.csv failures-total.csv > time+defining-onesided-only.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv failures.csv > time+defining-failure.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv clauses-total.csv > defining+total.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv failures-total.csv clauses-total-onesided.csv 1500000000 > clauses-defining-onesided.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv failures.csv 1500000000 > clauses-defining-failure.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv seconds-gen.csv > time-d4-gen.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen.csv seconds-check.csv > time-d4-verify.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv 25000 failures.csv > time-d4-failure.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen-onesided.csv seconds-check-onesided.csv > time-d4-verify-onesided.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen-onesided.csv seconds-check-onesided.csv failures-total.csv > time-d4-verify-onesided-only.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv seconds-gen.csv seconds-check.csv seconds-count.csv > times.csv
	$(INTERP) $(MERGE) -f clauses-total.csv clauses-total-nolemma.csv > clauses-lemma-nolemma.csv
	$(INTERP) $(MERGE) -f clauses-total.csv clauses-total-split.csv > clauses-nosplit-split.csv
	$(INTERP) $(MERGE) -f clauses-total.csv clauses-total-split+nolemma.csv > clauses-optimized-unoptimized.csv
	$(INTERP) $(MERGE) -f clauses-total.csv clauses-total-nolemma.csv clauses-total-split.csv clauses-total-split+nolemma.csv > clauses-optimizations.csv

	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.nolemma_log > seconds-gen-nolemma.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.nolemma_log > seconds-check-nolemma.csv
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.split_log > seconds-gen-split.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.split_log > seconds-check-split.csv
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.split_nolemma_log > seconds-gen-split+nolemma.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.split_nolemma_log > seconds-check-split+nolemma.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen.csv seconds-check.csv seconds-gen-split+nolemma.csv > time-verify-opt.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-nolemma.csv seconds-check-nolemma.csv > time-verify-nolemma.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-split.csv seconds-check-split.csv > time-verify-split.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-split+nolemma.csv seconds-check-split+nolemma.csv > time-verify-split+nolemma.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen.csv seconds-check.csv > time-structured.csv

	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.monolithic_log > seconds-gen-monolithic.csv
	$(INTERP) $(GRAB) "GEN OUTCOME: Timeout" *.monolithic_log > timeouts-monolithic.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.monolithic_log > seconds-check-monolithic.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.monolithic_log > clauses-total-monolithic.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen.csv seconds-check.csv > time-structured.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-monolithic.csv seconds-check-monolithic.csv \
		| sed 's/1943.193/1500/g' > time-monolithic.csv
	$(INTERP) $(MERGE) -f time-structured.csv time-monolithic.csv > time-structured+monolithic.csv
	$(INTERP) $(MERGE) -f time-structured.csv timeouts-monolithic.csv 1500 > time-structured+monolithic_timeout.csv
	$(INTERP) $(MERGE) -f clauses-total.csv clauses-total-monolithic.csv > clauses-total-structured+monolithic.csv


	$(INTERP) $(GRAB) "root model" *.mice_log > models-mice.csv
	$(INTERP) $(GRAB) "N2T ERROR: Timeout" *.mice_log > timeouts-mice.csv
#	$(INTERP) $(GRAB) "panick" *.mice_log > errors-mice.csv
	$(INTERP) $(GRAB) "N2T LOG: Elapsed" *.mice_log > seconds-n2t.csv
	$(INTERP) $(GRAB) "TC LOG: Elapsed" *.mice_log > seconds-tc.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-n2t.csv seconds-tc.csv >  time-mice.csv
	$(INTERP) $(MERGE) -f -s 1:2:3 seconds-gen.csv seconds-check.csv seconds-count.csv > time-ours.csv
	$(INTERP) $(MERGE) -f time-ours.csv time-mice.csv models-mice.csv \
		| sed 's/1436.934/1500/g' | sed 's/1875.151/1500/g'> time-mice-compare.csv
	$(INTERP) $(MERGE) -f timeouts-mice.csv time-ours.csv 1500 > time-mice-timeout.csv
#	$(INTERP) $(MERGE) -f errors-mice.csv time-ours.csv 1500 > time-mice-error.csv

	$(INTERP) $(GRAB) "LCHECK LOG: Elapsed" *.lean_log > seconds-check-lean.csv
	$(INTERP) $(MERGE) -f clauses-total.csv seconds-check.csv seconds-check-lean.csv > time-check-regular-lean.csv

