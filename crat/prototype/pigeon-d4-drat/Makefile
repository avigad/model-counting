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

