INTERP = python3
DSHARP = ~/repos/dsharp/dsharp
D4 = ~/repos/d4/d4
VLEVEL = 1
DDNNF = ../ddnnf.py
CHECK = ../crat_checker.py
N=5
BDIR = ../../../benchmarks/generators
PGEN = $(BDIR)/gen_pigeon.py
HDIR = ../crat-lrat
HINTIFY = $(HDIR)/hintify.sh

pst: pigeon-sat-tseitin-$(N).cnf
psd: pigeon-sat-direct-$(N).cnf

pst-all: pigeon-sat-tseitin-$(N).cnf pigeon-sat-tseitin-$(N).nnf pigeon-sat-tseitin-$(N).crat \
		pigeon-sat-tseitin-$(N).hinted_crat pigeon-sat-tseitin-$(N).hinted_check_data
	cat pigeon-sat-tseitin-$(N).nnf_data pigeon-sat-tseitin-$(N).crat_data \
		pigeon-sat-tseitin-$(N).hint_data pigeon-sat-tseitin-$(N).hinted_check_data \
		> pigeon-sat-tseitin-$(N).data

psd-all: pigeon-sat-direct-$(N).cnf pigeon-sat-direct-$(N).nnf pigeon-sat-direct-$(N).crat \
		pigeon-sat-direct-$(N).hinted_crat pigeon-sat-direct-$(N).hinted_check_data
	cat pigeon-sat-direct-$(N).nnf_data pigeon-sat-direct-$(N).crat_data \
		pigeon-sat-direct-$(N).hint_data pigeon-sat-direct-$(N).hinted_check_data \
		> pigeon-sat-direct-$(N).data

pst-d4all: pigeon-sat-tseitin-$(N).cnf pigeon-sat-tseitin-$(N).d4nnf pigeon-sat-tseitin-$(N).d4crat \
		pigeon-sat-tseitin-$(N).d4hinted_crat pigeon-sat-tseitin-$(N).d4hinted_check_data
	cat pigeon-sat-tseitin-$(N).d4nnf_data pigeon-sat-tseitin-$(N).d4crat_data \
		pigeon-sat-tseitin-$(N).d4hint_data pigeon-sat-tseitin-$(N).d4hinted_check_data \
		> pigeon-sat-tseitin-$(N).d4data

psd-d4all: pigeon-sat-direct-$(N).cnf pigeon-sat-direct-$(N).d4nnf pigeon-sat-direct-$(N).d4crat \
		pigeon-sat-direct-$(N).d4hinted_crat pigeon-sat-direct-$(N).d4hinted_check_data
	cat pigeon-sat-direct-$(N).d4nnf_data pigeon-sat-direct-$(N).d4crat_data \
		pigeon-sat-direct-$(N).d4hint_data pigeon-sat-direct-$(N).d4hinted_check_data \
		> pigeon-sat-direct-$(N).d4data


pigeon-sat-direct-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -r pigeon-sat-direct-$(N) -n $(N) -p $(N)

pigeon-sat-tseitin-$(N).cnf:
	$(INTERP) $(PGEN) -n $(N) -v -L -r pigeon-sat-tseitin-$(N) -n $(N) -p $(N)

.SUFFIXES: .cnf .nnf .crat .hinted_crat .hinted_check_data \
	      .d4nnf .d4crat .d4check_data .d4hinted_crat .d4hinted_check_data

.cnf.nnf:
	$(DSHARP) -Fnnf $@ $< | tee $*.nnf_data

.nnf.crat:
	$(INTERP) $(DDNNF) -i $*.cnf -n $< -p $@ -v $(VLEVEL) | tee $*.crat_data

.crat.hinted_crat:
	echo "Adding hints for $*.crat" | tee $*.hint_data
	{ /usr/bin/time -p $(HINTIFY) $* 2>&1 ; } | tee -a $*.hint_data
	mv $*.hcrat $@

.hinted_crat.hinted_check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $<  | tee $@

.cnf.d4nnf:
	$(D4) $< -dDNNF -out=$@ | tee $*.d4nnf_data

.d4nnf.d4crat:
	$(INTERP) $(DDNNF) -d -i $*.cnf -n $< -p $@ -v $(VLEVEL) | tee $*.d4crat_data

.d4crat.d4check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $< -o $*.d4hinted_crat | tee $@

.d4crat.d4hinted_crat:
	echo "Adding hints for $*.d4crat" | tee $*.d4hint_data
	{ /usr/bin/time -p $(HINTIFY) $* 2>&1 ; } | tee -a $*.d4hint_data
	mv $*.hcrat $@

.d4hinted_crat.d4hinted_check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $<  | tee $@


clean:
	rm -f *~

superclean: clean
	rm -f *.cnf *.nnf *.crat *.hinted_crat *data

