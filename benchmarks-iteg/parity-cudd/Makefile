TOP = ../..
GEN = $(TOP)/benchmarks/generators/parity.py
RUN = ~/repos/Cloud-BDD/runbdd
CONVERT = $(TOP)/translate/ddtrans.py
N=010

parity-$(N).iteg: $(GEN) $(CONVERT)
	$(GEN) $(N) parity-$(N).bdd > parity-$(N).cmd
	$(RUN) -f parity-$(N).cmd
	$(CONVERT) -i parity-$(N).bdd -I parity-$(N).iteg
	rm -f parity-$(N).cmd parity-$(N).bdd


clean:
	rm -f *~ *.cmd *.bdd

superclean: clean
	rm -f *.iteg
