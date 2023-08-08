INTERP = python3
TDIR = ../../../tools
GRAB = $(TDIR)/grab_data.py
MERGE = $(TDIR)/merge_csv.py
TWEAK = $(TDIR)/tweak_csv.py

data:
# D4
	$(INTERP) $(GRAB) "D4 LOG: Elapsed" *.D4_log > seconds-d4.csv
	$(INTERP) $(GRAB) -1 "Compressed POG has" *.D4_log > clauses-defining.csv
	$(INTERP) $(GRAB) -1 "tree size" *.D4_log > tree-ratio.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv tree-ratio.csv > d4-results.csv
# Mono
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.mono_log > seconds-gen-mono.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.mono_log > seconds-check-mono.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.mono_log > clauses-mono.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-mono.csv seconds-check-mono.csv > seconds-mono.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.mono_log > failures-mono.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv failures-mono.csv > clauses-failures-mono.csv

# Structured
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.structured_log > seconds-gen-structured.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.structured_log > seconds-check-structured.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.structured_log > clauses-structured.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-structured.csv seconds-check-structured.csv > seconds-structured.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.structured_log > failures-structured.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv failures-structured.csv > clauses-failures-structured.csv

# Hybrid
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.hybrid_log > seconds-gen-hybrid.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.hybrid_log > seconds-check-hybrid.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.hybrid_log > clauses-hybrid.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-hybrid.csv seconds-check-hybrid.csv > seconds-hybrid.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.hybrid_log > failures-hybrid.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv failures-hybrid.csv > clauses-failures-hybrid.csv

# Comparisons
	$(INTERP) $(MERGE) -f -r 7:4 clauses-defining.csv seconds-structured.csv seconds-mono.csv tree-ratio.csv > timing-structured-mono.csv
	$(INTERP) $(MERGE) -f clauses-structured.csv clauses-mono.csv > clauses-structured-mono.csv


clean:
	rm -f *~ *.csv
