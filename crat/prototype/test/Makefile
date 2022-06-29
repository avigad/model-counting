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
	$(INTERP) $(PGEN) -n $(N) -v -r pigeon-sat-tseitin-$(N) -n $(N) -p $(N)

pigeon-sat-tseitin-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -L -r pigeon-sat-tseitin-$(N) -n $(N) -p $(N)

.SUFFIXES: .cnf .nnf .crat .data

.cnf.nnf:
	$(DSHARP) -Fnnf $@ $<

.nnf.crat:
	$(INTERP) $(DDNNF) -i $*.cnf -n $< -p $@ -v $(VLEVEL)

.crat.data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $< | tee $@
