INTERP = python3
TDIR = ../../../tools
GRAB = $(TDIR)/grab_data.py
MERGE = $(TDIR)/merge_csv.py
TWEAK = $(TDIR)/tweak_csv.py

data:
	$(INTERP) $(GRAB) "D4 LOG: Elapsed" *.D4_log > seconds-d4.csv
	$(INTERP) $(GRAB) -1 "Compressed POG has" *.D4_log > clauses-defining.csv
	$(INTERP) $(GRAB) -1 "tree size" *.D4_log > tree-ratio.csv
	$(INTERP) $(MERGE) -f seconds-d4.csv clauses-defining.csv tree-ratio.csv > d4-results.csv

clean:
	rm -f *~ *.csv
