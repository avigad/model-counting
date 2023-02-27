INTERP = python3
TDIR = ../../../tools
GRAB = $(TDIR)/grab_data.py
MERGE = $(TDIR)/merge_csv.py

data:
	$(INTERP) $(GRAB) "D4 LOG: Elapsed" *.D4_log > seconds-d4.csv
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.log > seconds-gen.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.log > seconds-check.csv
	$(INTERP) $(GRAB) "COUNT LOG: Elapsed" *.log > seconds-count.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.log > failures.csv
	$(INTERP) $(GRAB) -1 "Compressed POG has" *.D4_log > clauses-defining.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.log > clauses-total.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.nolemma_log > clauses-total-nolemma.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.split_log > clauses-total-split.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.split_nolemma_log > clauses-total-split+nolemma.csv


	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv > time+defining.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv clauses-total.csv > time+defining-success.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv failures.csv > time+defining-failure.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv clauses-total.csv > defining+total.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv seconds-gen.csv > time-d4-gen.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen.csv seconds-check.csv > time-d4-verify.csv
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
