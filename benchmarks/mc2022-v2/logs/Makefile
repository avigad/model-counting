
TDIR = ../../../tools
GRAB = $(TDIR)/grab_data.py
MERGE = $(TDIR)/merge_csv.py
EXTRACT = $(TDIR)/extract_columns.py
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
	$(INTERP) $(GRAB) "GEN ERROR" *.hybrid_onesided_log > failures-hybrid.csv
	$(INTERP) $(GRAB) "CHECK: Elapsed" *.hybrid_onesided_log > seconds-gen-onesided.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.hybrid_onesided_log > seconds-check-onesided.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen-hybrid.csv seconds-check-hybrid.csv > seconds-summary.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen-onesided.csv seconds-check-onesided.csv > seconds-summary-onesided.csv
	$(INTERP) $(MERGE) -f seconds-gen-onesided.csv clauses-defining.csv 2500000000 > clauses-summary-onesided.csv
	$(INTERP) $(MERGE) -f failures-hybrid.csv seconds-d4.csv 25000 > seconds-summary-failures.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv clauses-hybrid.csv > clauses-summary.csv
	$(INTERP) $(MERGE) -f failures-hybrid.csv clauses-defining.csv 2500000000 > clauses-summary-failures.csv


#Structured Only
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.structured_only_log > seconds-gen-structured-only.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.structured_only_log > seconds-check-structured-only.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.structured_only_log > clauses-structured-only.csv
	$(INTERP) $(MERGE) -f -s 2:3 seconds-d4.csv seconds-gen-structured-only.csv seconds-check-structured-only.csv > seconds-summary-structured-only.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv clauses-structured-only.csv > clauses-summary-structured-only.csv


# Mono
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.mono_log > seconds-gen-mono.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.mono_log > seconds-check-mono.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.mono_log > clauses-mono.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-mono.csv seconds-check-mono.csv > seconds-mono.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.mono_log > failures-mono.csv
	$(INTERP) $(MERGE) -f -t 3:1000:1500 sub10M.arch-csv seconds-mono.csv > sub10M-seconds-mono-all.csv
	$(INTERP) $(EXTRACT) 1:5 < sub10M-seconds-mono-all.csv > sub10M-seconds-ok-mono.csv
	$(INTERP) $(MERGE) -f -t 2:999:1500 sub10M.arch-csv seconds-d4.csv failures-mono.csv > sub10M-seconds-failures-mono-all.csv
	$(INTERP) $(EXTRACT) 1:4 < sub10M-seconds-failures-mono-all.csv > sub10M-seconds-failures-mono.csv
	cat sub10M-seconds-ok-mono.csv sub10M-seconds-failures-mono.csv > sub10M-seconds-mono.csv
	$(INTERP) $(MERGE) -f -o 1:1000 sub10M-seconds-ok-mono.csv clauses-mono.csv > sub10M-clauses-mono-all.csv
	$(INTERP) $(EXTRACT) 1:3 < sub10M-clauses-mono-all.csv > sub10M-clauses-ok-mono.csv
	$(INTERP) $(MERGE) -f -o -1:1000 sub10M-seconds-mono.csv 25000000 > sub10M-clauses-toobig-mono-all.csv
	$(INTERP) $(EXTRACT) 1:3 < sub10M-clauses-toobig-mono-all.csv > sub10M-clauses-toobig-mono.csv
	cat sub10M-clauses-ok-mono.csv sub10M-clauses-toobig-mono.csv > sub10M-clauses-mono.csv

# Structured
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.structured_log > seconds-gen-structured.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.structured_log > seconds-check-structured.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.structured_log > clauses-structured.csv
	$(INTERP) $(MERGE) -f -s 1:2 seconds-gen-structured.csv seconds-check-structured.csv > seconds-structured.csv
	$(INTERP) $(GRAB) "GEN ERROR" *.structured_log > failures-structured.csv
	$(INTERP) $(MERGE) -f -t 3:1000:1500 sub10M.arch-csv seconds-structured.csv > sub10M-seconds-structured-all.csv
	$(INTERP) $(EXTRACT) 1:5 < sub10M-seconds-structured-all.csv > sub10M-seconds-ok-structured.csv
	$(INTERP) $(MERGE) -f -t 2:999:1500 sub10M.arch-csv seconds-d4.csv failures-structured.csv > sub10M-seconds-failures-structured-all.csv
	$(INTERP) $(EXTRACT) 1:4 < sub10M-seconds-failures-structured-all.csv > sub10M-seconds-failures-structured.csv
	cat sub10M-seconds-ok-structured.csv sub10M-seconds-failures-structured.csv > sub10M-seconds-structured.csv
	$(INTERP) $(MERGE) -f -o 1:1000 sub10M-seconds-ok-structured.csv clauses-structured.csv > sub10M-clauses-structured-all.csv
	$(INTERP) $(EXTRACT) 1:3 < sub10M-clauses-structured-all.csv > sub10M-clauses-ok-structured.csv
	$(INTERP) $(MERGE) -f -o -1:1000 sub10M-seconds-structured.csv 25000000 > sub10M-clauses-toobig-structured-all.csv
	$(INTERP) $(EXTRACT) 1:3 < sub10M-clauses-toobig-structured-all.csv > sub10M-clauses-toobig-structured.csv
	cat sub10M-clauses-ok-structured.csv sub10M-clauses-toobig-structured.csv > sub10M-clauses-structured.csv

#

#       Comparisons
	$(INTERP) $(MERGE) -f -o  1:5 tree-ratio.csv sub10M-seconds-mono.csv sub10M-seconds-structured.csv | \
		grep -v 1500,1500 > sub10M-seconds-subthresh.csv
	$(INTERP) $(MERGE) -f -o -1:5 tree-ratio.csv sub10M-seconds-mono.csv sub10M-seconds-structured.csv | \
		grep -v 1500,1500 > sub10M-seconds-supthresh.csv
	$(INTERP) $(MERGE) -f -o  1:5 tree-ratio.csv sub10M-clauses-mono.csv sub10M-clauses-structured.csv | \
		grep -v 25000000,25000000 > sub10M-clauses-subthresh.csv 
	$(INTERP) $(MERGE) -f -o -1:5 tree-ratio.csv sub10M-clauses-mono.csv sub10M-clauses-structured.csv | \
		grep -v 25000000,25000000 > sub10M-clauses-supthresh.csv



clean:
	rm -f *~ *.csv
