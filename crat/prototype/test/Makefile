INTERP = python3
DSHARP = ~/repos/dsharp/dsharp
D4 = ~/repos/d4/d4
VLEVEL = 2
HLEVEL = 4
LHEIGHT = 2
DDNNF = ../ddnnf.py
CHECK = ../crat_checker.py

.SUFFIXES: .cnf .nnf .crat .check_data .hinted_crat .hinted_check_data \
	      .d4nnf .d4crat .d4check_data .d4hinted_crat .d4hinted_check_data

.cnf.nnf:
	$(DSHARP) -Fnnf $@ $< | tee $*.nnf_data

.nnf.crat:
	$(INTERP) $(DDNNF) -i $*.cnf -n $< -p $@ -v $(VLEVEL) -H $(HLEVEL) -L $(LHEIGHT) | tee $*.crat_data

.crat.check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $< -o $*.hinted_crat | tee $@

.hinted_crat.hinted_check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $<  | tee $@

.cnf.d4nnf:
	$(D4) $< -dDNNF -out=$@ | tee $*.d4nnf_data

.d4nnf.d4crat:
	$(INTERP) $(DDNNF) -d -i $*.cnf -n $< -p $@ -v $(VLEVEL) -H $(HLEVEL) -L $(LHEIGHT) | tee $*.d4crat_data

.d4crat.d4check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $< -o $*.d4hinted_crat | tee $@

.d4hinted_crat.d4hinted_check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $<  | tee $@
