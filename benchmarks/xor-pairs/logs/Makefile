INTERP = python3
TDIR = ../../../tools
GRAB = $(TDIR)/grab_data.py
PGRAB = $(TDIR)/grab_prob.py
MERGE = $(TDIR)/merge_csv.py

data:
	$(INTERP) $(PGRAB) xp*.log > problem-sizes.csv
	$(INTERP) $(GRAB) -1 "Compressed POG has" xp*.log > clauses-defining.csv
	$(INTERP) $(GRAB) "clause TOTAL" xp*.log > clauses-total.csv
	$(INTERP) $(MERGE) -f problem-sizes.csv clauses-defining.csv > defining.csv
	$(INTERP) $(MERGE) -f problem-sizes.csv clauses-total.csv > total.csv
	$(INTERP) $(MERGE)  problem-sizes.csv clauses-defining.csv clauses-total.csv > all.csv
