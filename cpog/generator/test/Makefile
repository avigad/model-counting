INTERP = python3
DSHARP = ~/repos/dsharp/dsharp
TBSAT = ~/repos/tbuddy/tbsat/src/tbsat
D4 = ~/repos/d4/d4
D2P = ../d2p
VLEVEL = 2
CHECK = ../../checker/crat-check
B2P = ../../prototype/btrace2pog.py
D2P_OPTIONS=


.SUFFIXES: .cnf \
	.d4nnf .d4_dt_crat .d4_dt_check_data \
	.d4_rup_crat .d4_rup_check_data \
	.d4_rup_mcrat .d4_rup_mcheck_data \
	.d4_rup_ecrat .d4_rup_echeck_data \
	.btrace .bcrat .bcheck_data

.cnf.d4nnf:
	$(D4) $< -dDNNF -out=$@ | tee $*.d4nnf_data

.d4nnf.d4_rup_crat:
	$(D2P) -v $(VLEVEL) $(D2P_OPTIONS) $*.cnf $< $@ | tee $*.d4_rup_crat_data

.d4nnf.d4_rup_mcrat:
	$(D2P) -m -v $(VLEVEL) $(D2P_OPTIONS) $*.cnf $< $@ | tee $*.d4_rup_crat_data

.d4_rup_crat.d4_rup_check_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@

.d4_rup_mcrat.d4_rup_mcheck_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@

.d4nnf.d4_rup_ecrat:
	$(D2P) -e -v $(VLEVEL) $(D2P_OPTIONS) $*.cnf $< $@ | tee $*.d4_rup_ecrat_data

.d4_rup_ecrat.d4_rup_echeck_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@


.d4nnf.d4_dt_crat:
	$(D2P) -t -v $(VLEVEL) $(D2P_OPTIONS) $*.cnf $< $@ | tee $*.d4_dt_crat_data

.d4_dt_crat.d4_dt_check_data:
	$(CHECK) -v $(VLEVEL) $*.cnf $< | tee $@


.cnf.btrace:
	$(TBSAT) -v $(VLEVEL) -m 0 -i $< -o $*.lrat -T $@

.btrace.bcrat:
	$(INTERP) $(B2P) -v $(VLEVEL) -i $*.cnf -b $< -c $@

.bcrat.bcheck_data:
	$(INTERP) $(CHECK) -v $(VCLEVEL) -i $*.cnf -p $< | tee $@

clean:
	rm -f *~ reduction-1*.cnf rm -f *~ reduction-1*.lrat

superclean: clean
	rm -f *.d4crat *.d4crat_data *.d4nnf_data *.d4check_data *.btrace *.bcrat *.bcheck_data reduction-*.cnf
