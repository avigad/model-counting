INTERP = python3
TDIR = ../../../tools
GRAB = $(TDIR)/grab_data.py
MERGE = $(TDIR)/merge_csv.py

data:
	$(INTERP) $(GRAB) "D4 LOG: Elapsed" *.D4_log > seconds-d4.csv
	$(INTERP) $(GRAB) "GEN LOG: Elapsed" *.log > seconds-gen.csv
	$(INTERP) $(GRAB) "FCHECK LOG: Elapsed" *.log > seconds-check.csv
	$(INTERP) $(GRAB) "COUNT LOG: Elapsed" *.log > seconds-count.csv
	$(INTERP) $(GRAB) -1 "Compressed POG has" *.D4_log > clauses-defining.csv
	$(INTERP) $(GRAB) "clause TOTAL" *.log > clauses-total.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv > time+defining.csv
	$(INTERP) $(MERGE) -f clauses-defining.csv clauses-total.csv > defining+total.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv seconds-gen.csv > time-d4-gen.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv seconds-gen.csv seconds-check.csv seconds-count.csv > times.csv
