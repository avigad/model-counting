INTERP = python3
DSHARP = ~/repos/dsharp/dsharp
VERB = -v
DDNNF = ../ddnnf.py
CHECK = ../crat_checker.py
LAX = -L

.SUFFIXES: .cnf .nnf .crat .data

.cnf.nnf:
	$(DSHARP) -Fnnf $@ $<

.nnf.crat:
	$(INTERP) $(DDNNF) -i $*.cnf -n $< -p $@ $(VERB)

.crat.data:
	$(INTERP) $(CHECK) $(VERB) $(LAX) -i $*.cnf -p $< | tee $@
