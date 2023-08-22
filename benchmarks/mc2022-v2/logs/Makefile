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

# Summary
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.hybrid_log > seconds-gen-hybrid.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.hybrid_log > seconds-check-hybrid.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.hybrid_log > clauses-hybrid.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.hybrid_log > failures-hybrid.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen-hybrid.csv seconds-check-hybrid.csv > seconds-summary.csv
	$(INTERP) $(MERGE) -f failures-hybrid.csv seconds-d4.csv 25000 > seconds-summary-failures.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv clauses-hybrid.csv > clauses-summary.csv
	$(INTERP) $(MERGE) -f failures-hybrid.csv clauses-defining.csv 1500000000 > clauses-summary-failures.csv

# Mono
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.mono_log > seconds-gen-mono.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.mono_log > seconds-check-mono.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.mono_log > clauses-mono.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-mono.csv seconds-check-mono.csv > seconds-mono.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.mono_log > failures-mono.csv
	$(INTERP) $(MERGE) -f -t 4:1000:1500 sub10M.arch-csv seconds-d4.csv seconds-mono.csv > sub10M-seconds-mono.csv
	$(INTERP) $(MERGE) -f -t 2:999:1500 sub10M.arch-csv seconds-d4.csv failures-mono.csv > sub10M-seconds-failures-mono.csv
	$(INTERP) $(MERGE) -f -o 5:1000 sub10M-seconds-mono.csv clauses-defining.csv clauses-mono.csv > sub10M-clauses-mono.csv
	$(INTERP) $(MERGE) -f sub10M.arch-csv failures-mono.csv clauses-defining.csv 15000000 > sub10M-clauses-failures-mono.csv
	$(INTERP) $(MERGE) -f -o -5:1000 sub10M-seconds-mono.csv clauses-defining.csv 15000000 > sub10M-clauses-toobig-mono.csv

# Structured
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.structured_log > seconds-gen-structured.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.structured_log > seconds-check-structured.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.structured_log > clauses-structured.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.structured_log > failures-structured.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-structured.csv seconds-check-structured.csv > seconds-structured.csv

	$(INTERP) $(MERGE) -f -t 4:1000:1500 sub10M.arch-csv seconds-d4.csv seconds-structured.csv > sub10M-seconds-structured.csv
	$(INTERP) $(MERGE) -f -t 2:999:1500 sub10M.arch-csv seconds-d4.csv failures-structured.csv > sub10M-seconds-failures-structured.csv
	$(INTERP) $(MERGE) -f -o 5:1000 sub10M-seconds-structured.csv clauses-defining.csv clauses-structured.csv > sub10M-clauses-structured.csv
	$(INTERP) $(MERGE) -f sub10M.arch-csv failures-structured.csv clauses-defining.csv 15000000 > sub10M-clauses-failures-structured.csv
	$(INTERP) $(MERGE) -f -o -5:1000 sub10M-seconds-structured.csv clauses-defining.csv 15000000 > sub10M-clauses-toobig-structured.csv

# Hybrid
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-hybrid.csv seconds-check-hybrid.csv > seconds-hybrid.csv

	$(INTERP) $(MERGE) -f -t 4:1000:1500 sub10M.arch-csv seconds-d4.csv seconds-hybrid.csv > sub10M-seconds-hybrid.csv
	$(INTERP) $(MERGE) -f -t 2:999:1500 sub10M.arch-csv seconds-d4.csv failures-hybrid.csv > sub10M-seconds-failures-hybrid.csv
	$(INTERP) $(MERGE) -f -o 5:1000 sub10M-seconds-hybrid.csv clauses-defining.csv clauses-hybrid.csv > sub10M-clauses-hybrid.csv
	$(INTERP) $(MERGE) -f sub10M.arch-csv failures-hybrid.csv clauses-defining.csv 15000000 > sub10M-clauses-failures-hybrid.csv
	$(INTERP) $(MERGE) -f -o -5:1000 sub10M-seconds-hybrid.csv clauses-defining.csv 15000000 > sub10M-clauses-toobig-hybrid.csv



clean:
	rm -f *~ *.csv
