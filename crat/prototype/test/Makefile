INTERP = python3
DSHARP = ~/repos/dsharp/dsharp
VLEVEL = 1
DDNNF = ../ddnnf.py
CHECK = ../crat_checker.py

.SUFFIXES: .cnf .nnf .crat .check_data .hinted_crat .hinted_check_data

.cnf.nnf:
	$(DSHARP) -Fnnf $@ $< | tee $*.nnf_data

.nnf.crat:
	$(INTERP) $(DDNNF) -i $*.cnf -n $< -p $@ -v $(VLEVEL) | tee $*.crat_data

.crat.check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $< -o $*.hinted_crat | tee $@

.hinted_crat.hinted_check_data:
	$(INTERP) $(CHECK) -v $(VLEVEL) -i $*.cnf -p $<  | tee $@
