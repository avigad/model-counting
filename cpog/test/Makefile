INTERP = python3
DSHARP = ~/repos/dsharp/dsharp
D4 = ~/repos/d4/d4
GEN=../generator/cpog-generate
OGEN=../generator/ocpog-generate
CHECK=../checker/cpog-check
COUNT=../counter/cpog-count.py
VLEVEL = 2
GEN_OPTIONS=

.SUFFIXES: .cnf .nnf .cpog .check_data \
	.mcpog .mcheck_data .ecpog .echeck_data \
	.ocpog .ocheck_data

.cnf.nnf:
	$(D4) $< -dDNNF -out=$@ | tee $*.d4nnf_data

.nnf.cpog:
	$(GEN) -v $(VLEVEL) $(GEN_OPTIONS) $*.cnf $< $@ | tee $*.cpog_data

.cpog.check_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@

.nnf.ocpog:
	$(OGEN) -v $(VLEVEL) $(GEN_OPTIONS) $*.cnf $< $@ | tee $*.ocpog_data

.ocpog.ocheck_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@


.nnf.mcpog:
	$(GEN) -m -v $(VLEVEL) $(GEN_OPTIONS) $*.cnf $< $@ | tee $*.mcpog_data

.mcpog.mcheck_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@

.nnf.ecpog:
	$(GEN) -m -v $(VLEVEL) $(GEN_OPTIONS) $*.cnf $< $@ | tee $*.ecpog_data

.ecpog.echeck_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@


clean:
	rm -f *~ reduction-1*.cnf rm -f *~ reduction-1*.lrat

superclean: clean
	rm -f *_data *pog
