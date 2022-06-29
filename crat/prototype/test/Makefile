INTERP = python3.9
DSHARP = ~/repos/dsharp/dsharp
VLEVEL = 1
DDNNF = ../ddnnf.py
CHECK = ../crat_checker.py
N=5
BDIR = ../../../benchmarks/generators
PGEN = $(BDIR)/gen_pigeon.py

pst: pigeon-sat-tseitin-$(N).cnf
pdt: pigeon-sat-direct-$(N).cnf

pigeon-sat-direct-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -r pigeon-sat-direct-$(N) -n $(N) -p $(N)

pigeon-sat-tseitin-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -L -r pigeon-sat-tseitin-$(N) -n $(N) -p $(N)

.SUFFIXES: .cnf .nnf .crat .check_data

.cnf.nnf:
	$(DSHARP) -Fnnf $@ $< | tee $*.nnf_data

.nnf.crat:
	$(INTERP) $(DDNNF) -i $*.cnf -n $< -p $@ -v $(VLEVEL) | tee $*.crat_data

.crat.check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $< | tee $@
