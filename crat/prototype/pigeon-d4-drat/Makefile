INTERP = python3
D4 = ~/repos/d4/d4
VLEVEL = 1
VCLEVEL = 1
HLEVEL = 2
LHEIGHT = 2
DDNNF = ../ddnnf.py
CHECK = ../crat_checker.py
N=5
BDIR = ../../../benchmarks/generators
PGEN = $(BDIR)/gen_pigeon.py
HINTIFY = ../hintify.py
GRAB = ../../../tools/grab_data.py
MERGE = ../../../tools/merge_csv.py

pst: pigeon-sat-tseitin-$(N).cnf
psd: pigeon-sat-direct-$(N).cnf

pst-all: pigeon-sat-tseitin-$(N).cnf pigeon-sat-tseitin-$(N).nnf pigeon-sat-tseitin-$(N).crat \
		pigeon-sat-tseitin-$(N).hcrat pigeon-sat-tseitin-$(N).check_data
	cat pigeon-sat-tseitin-$(N).nnf_data pigeon-sat-tseitin-$(N).crat_data \
		pigeon-sat-tseitin-$(N).hint_data pigeon-sat-tseitin-$(N).check_data \
		> pigeon-sat-tseitin-$(N).data

psd-all: pigeon-sat-direct-$(N).cnf pigeon-sat-direct-$(N).nnf pigeon-sat-direct-$(N).crat \
		pigeon-sat-direct-$(N).hcrat pigeon-sat-direct-$(N).check_data
	cat pigeon-sat-direct-$(N).nnf_data pigeon-sat-direct-$(N).crat_data \
		pigeon-sat-direct-$(N).hint_data pigeon-sat-direct-$(N).check_data \
		> pigeon-sat-direct-$(N).data

pigeon-sat-direct-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -r pigeon-sat-direct-$(N) -n $(N) -p $(N)

pigeon-sat-tseitin-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -L -r pigeon-sat-tseitin-$(N) -n $(N) -p $(N)

.SUFFIXES: .cnf .nnf .crat .hcrat .check_data

.cnf.nnf:
	$(D4) $< -dDNNF -out=$@ | tee $*.nnf_data

.nnf.crat:
	$(INTERP) $(DDNNF) -d -i $*.cnf -n $< -p $@ -v $(VLEVEL) -H $(HLEVEL) -L $(LHEIGHT) -s | tee $*.crat_data

.crat.hcrat:
	$(INTERP) $(HINTIFY) -i $*.cnf -p $< -o $@ | tee $*.hint_data

.hcrat.check_data:
	$(INTERP) $(CHECK) -v $(VCLEVEL) -i $*.cnf -p $< -o $*.hinted_crat | tee $@


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.nnf *.crat *data

data:
	$(INTERP) $(GRAB) -1 "Input NNF" pigeon-sat-direct-*.data > psd-nnf-nodes.csv
	$(INTERP) $(GRAB) -1 "Input NNF" pigeon-sat-tseitin-*.data > pst-nnf-nodes.csv
	$(INTERP) $(GRAB) "Generated POG" pigeon-sat-direct-*.data > psd-pog-nodes.csv
	$(INTERP) $(GRAB) "Generated POG" pigeon-sat-tseitin-*.data > pst-pog-nodes.csv
	$(INTERP) $(GRAB) -1 "Total clauses" pigeon-sat-direct-*.data > psd-total-clauses.csv
	$(INTERP) $(GRAB) -1 "Total clauses" pigeon-sat-tseitin-*.data > pst-total-clauses.csv
	$(INTERP) $(GRAB)  2 "Total clauses" pigeon-sat-direct-*.data > psd-defining-clauses.csv
	$(INTERP) $(GRAB)  2 "Total clauses" pigeon-sat-tseitin-*.data > pst-defining-clauses.csv
	$(INTERP) $(GRAB)  5 "Total clauses" pigeon-sat-direct-*.data > psd-justification-clauses.csv
	$(INTERP) $(GRAB)  5 "Total clauses" pigeon-sat-tseitin-*.data > pst-justification-clauses.csv
	$(INTERP) $(GRAB) "GEN: Elapsed time" pigeon-sat-direct-*.data > psd-generate-seconds.csv
	$(INTERP) $(GRAB) "GEN: Elapsed time" pigeon-sat-tseitin-*.data > pst-generate-seconds.csv
	$(INTERP) $(GRAB) -1 "HINTIFY: Elapsed seconds" pigeon-sat-direct-*.data > psd-hintify-seconds.csv
	$(INTERP) $(GRAB) -1 "HINTIFY: Elapsed seconds" pigeon-sat-tseitin-*.data > pst-hintify-seconds.csv
	$(INTERP) $(GRAB) "CHECKER: Elapsed time" pigeon-sat-direct-*.data > psd-check-seconds.csv
	$(INTERP) $(GRAB) "CHECKER: Elapsed time" pigeon-sat-tseitin-*.data > pst-check-seconds.csv
	$(INTERP) $(MERGE) -l "NNF nodes,POG nodes,Def clauses,Just clauses,Tot clauses,Gen secs,Hint secs,Check secs" \
		pst-nnf-nodes.csv pst-pog-nodes.csv pst-defining-clauses.csv pst-justification-clauses.csv pst-total-clauses.csv \
		pst-generate-seconds.csv pst-hintify-seconds.csv pst-check-seconds.csv > pst-data.csv
	$(INTERP) $(MERGE) -l "NNF nodes,POG nodes,Def clauses,Just clauses,Tot clauses,Gen secs,Hint secs,Check secs" \
		psd-nnf-nodes.csv psd-pog-nodes.csv psd-defining-clauses.csv psd-justification-clauses.csv psd-total-clauses.csv \
		psd-generate-seconds.csv psd-hintify-seconds.csv psd-check-seconds.csv > psd-data.csv







