INTERP = python3
D4 = ~/repos/d4/d4
VLEVEL = 1
D2P = ../d2p
CHECK = ../../checker/crat-check
N=5
BDIR = ../../../benchmarks/generators
PGEN = $(BDIR)/gen_pigeon.py
GRAB = ../../../tools/grab_data.py
MERGE = ../../../tools/merge_csv.py

pst: pigeon-sat-tseitin-$(N).cnf
psd: pigeon-sat-direct-$(N).cnf

pst-all: pigeon-sat-tseitin-$(N).cnf pigeon-sat-tseitin-$(N).nnf pigeon-sat-tseitin-$(N).crat \
		pigeon-sat-tseitin-$(N).check_data
	cat pigeon-sat-tseitin-$(N).nnf_data pigeon-sat-tseitin-$(N).crat_data \
		pigeon-sat-tseitin-$(N).check_data \
		> pigeon-sat-tseitin-$(N).data

psd-all: pigeon-sat-direct-$(N).cnf pigeon-sat-direct-$(N).nnf pigeon-sat-direct-$(N).crat \
		pigeon-sat-direct-$(N).check_data
	cat pigeon-sat-direct-$(N).nnf_data pigeon-sat-direct-$(N).crat_data \
		pigeon-sat-direct-$(N).check_data \
		> pigeon-sat-direct-$(N).data

pigeon-sat-direct-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -r pigeon-sat-direct-$(N) -n $(N) -p $(N)

pigeon-sat-tseitin-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -L -r pigeon-sat-tseitin-$(N) -n $(N) -p $(N)

.SUFFIXES: .cnf .nnf .crat .check_data 

.cnf.nnf:
	$(D4) $< -no-rnd-init -dDNNF -out=$@ | tee $*.nnf_data

.nnf.crat:
	$(D2P) -v $(VLEVEL) -r $*.cnf $< $@  | tee $*.crat_data

.crat.check_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $<  | tee $@

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.nnf *.crat *data

data:
	$(INTERP) $(GRAB) "Read D4 NNF" pigeon-sat-direct-*.data > psd-nnf-nodes.csv
	$(INTERP) $(GRAB) "Read D4 NNF" pigeon-sat-tseitin-*.data > pst-nnf-nodes.csv
	$(INTERP) $(GRAB) "node TOTAL" pigeon-sat-direct-*.data > psd-pog-nodes.csv
	$(INTERP) $(GRAB) "node TOTAL" pigeon-sat-tseitin-*.data > pst-pog-nodes.csv
	$(INTERP) $(GRAB) "visit TOTAL" pigeon-sat-direct-*.data > psd-pog-node-visits.csv
	$(INTERP) $(GRAB) "visit TOTAL" pigeon-sat-tseitin-*.data > pst-pog-node-visits.csv
	$(INTERP) $(GRAB) "clause TOTAL" pigeon-sat-direct-*.data > psd-total-clauses.csv
	$(INTERP) $(GRAB) "clause TOTAL" pigeon-sat-tseitin-*.data > pst-total-clauses.csv
	$(INTERP) $(GRAB) "literal justification" pigeon-sat-direct-*.data > psd-justification-clauses.csv
	$(INTERP) $(GRAB) "literal justification" pigeon-sat-tseitin-*.data > pst-justification-clauses.csv
	$(INTERP) $(GRAB) "Final time:" pigeon-sat-direct-*.data > psd-d4-seconds.csv
	$(INTERP) $(GRAB) "Final time:" pigeon-sat-tseitin-*.data > pst-d4-seconds.csv
	$(INTERP) $(GRAB) "SAT execution" pigeon-sat-direct-*.data > psd-sat-seconds.csv
	$(INTERP) $(GRAB) "SAT execution" pigeon-sat-tseitin-*.data > pst-sat-seconds.csv
	$(INTERP) $(GRAB) "time TOTAL" pigeon-sat-direct-*.data > psd-generate-seconds.csv
	$(INTERP) $(GRAB) "time TOTAL" pigeon-sat-tseitin-*.data > pst-generate-seconds.csv
	$(INTERP) $(GRAB) "FCHECK: Elapsed" pigeon-sat-direct-*.data > psd-check-seconds.csv
	$(INTERP) $(GRAB) "FCHECK: Elapsed" pigeon-sat-tseitin-*.data > pst-check-seconds.csv
	$(INTERP) $(MERGE) -l "N,NNF nodes,POG nodes,Visit nodes,Just clauses,Tot clauses,D4 secs,SAT secs,Gen secs,Check secs" \
		pst-nnf-nodes.csv pst-pog-nodes.csv pst-pog-node-visits.csv pst-justification-clauses.csv pst-total-clauses.csv \
		pst-d4-seconds.csv pst-sat-seconds.csv \
		pst-generate-seconds.csv pst-check-seconds.csv > pst-d4-rup-data.csv
	$(INTERP) $(MERGE) -l "N,NNF nodes,POG nodes,Visit nodes,Just clauses,Tot clauses,D4 secs,SAT secs,Gen secs,Check secs" \
		psd-nnf-nodes.csv psd-pog-nodes.csv psd-pog-node-visits.csv psd-justification-clauses.csv psd-total-clauses.csv \
		psd-d4-seconds.csv psd-sat-seconds.csv \
		psd-generate-seconds.csv psd-check-seconds.csv > psd-d4-rup-data.csv

