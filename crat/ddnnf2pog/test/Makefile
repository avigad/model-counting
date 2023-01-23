INTERP = python3
DSHARP = ~/repos/dsharp/dsharp
TBSAT = ~/repos/tbuddy/tbsat/src/tbsat
D4 = ~/repos/d4/d4
D2P = ../d2p
VLEVEL = 2
CHECK = ../../checker/crat-check
B2P = ../../prototype/btrace2pog.py


.SUFFIXES: .cnf \
	.d4nnf .d4crat .d4check_data \
	.btrace .bcrat .bcheck_data

.cnf.d4nnf:
	$(D4) $< -dDNNF -out=$@ | tee $*.d4nnf_data

.d4nnf.d4crat:
	$(D2P) $(VLEVEL) $*.cnf $< $@ | tee $*.d4crat_data

.d4crat.d4check_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@

.cnf.btrace:
	$(TBSAT) -v $(VLEVEL) -m 0 -i $< -o $*.lrat -T $@

.btrace.bcrat:
	$(INTERP) $(B2P) -v $(VLEVEL) -i $*.cnf -b $< -c $@

.bcrat.bcheck_data:
	$(INTERP) $(CHECK) -v $(VCLEVEL) -i $*.cnf -p $< | tee $@

clean:
	rm -f *~ reduction-1*.cnf

superclean: clean
	rm -f *.d4crat *.d4crat_data *.d4nnf_data *.d4check_data *.btrace *.bcrat *.bcheck_data reduction-*.cnf
