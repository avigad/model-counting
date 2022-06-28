INTERP = python3.9
DSHARP = ~/repos/dsharp/dsharp
VLEVEL = 3
DDNNF = ../ddnnf.py
CHECK = ../crat_checker.py
#LAX = -L
LAX =

.SUFFIXES: .cnf .nnf .crat .data

.cnf.nnf:
	$(DSHARP) -Fnnf $@ $<

.nnf.crat:
	$(INTERP) $(DDNNF) -i $*.cnf -n $< -p $@ -v $(VLEVEL)

.crat.data:
	$(INTERP) $(CHECK) -v $(VLEVEL) $(LAX) -i $*.cnf -p $< | tee $@
