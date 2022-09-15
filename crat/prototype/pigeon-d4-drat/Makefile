INTERP = python3
D4 = ~/repos/d4/d4
VLEVEL = 1
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
		pigeon-sat-tseitin-$(N).drat
	cat pigeon-sat-tseitin-$(N).nnf_data pigeon-sat-tseitin-$(N).crat_data \
		pigeon-sat-tseitin-$(N).drat_data \
		> pigeon-sat-tseitin-$(N).data

psd-all: pigeon-sat-direct-$(N).cnf pigeon-sat-direct-$(N).nnf pigeon-sat-direct-$(N).crat \
		pigeon-sat-direct-$(N).drat
	cat pigeon-sat-direct-$(N).nnf_data pigeon-sat-direct-$(N).crat_data \
		pigeon-sat-direct-$(N).drat_data \
		> pigeon-sat-direct-$(N).data

pigeon-sat-direct-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -r pigeon-sat-direct-$(N) -n $(N) -p $(N)

pigeon-sat-tseitin-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -L -r pigeon-sat-tseitin-$(N) -n $(N) -p $(N)

.SUFFIXES: .cnf .nnf .crat .drat


.cnf.nnf:
	$(D4) $< -dDNNF -out=$@ | tee $*.nnf_data

.nnf.crat:
	$(INTERP) $(DDNNF) -d -i $*.cnf -n $< -p $@ -v $(VLEVEL) -H $(HLEVEL) -L $(LHEIGHT) -s | tee $*.crat_data

.crat.drat:
	$(INTERP) $(HINTIFY) -i $*.cnf -p $< -r $* | tee $*.drat_data

clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.nnf *.crat *data

