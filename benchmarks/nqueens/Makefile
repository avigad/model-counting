TOP = ../..
GEN = $(TOP)/benchmarks/generators/lqueen.py
RUN = ~/repos/Cloud-BDD/runbdd
CONVERT = $(TOP)/translate/ddtrans.py
N=04

nqueen-$(N).iteg: $(GEN) $(CONVERT)
	$(GEN) -A -n $(N) -s nqueen-$(N).bdd
	$(RUN) -f lqa$(N)-onh-fast-q.cmd
	$(CONVERT) -i nqueen-$(N).bdd -I nqueen-$(N).iteg
	rm -f lqa$(N)-onh-fast-q.cmd nqueen-$(N).bdd

clean:
	rm -f *~ *.cmd *.bdd

superclean: clean
	rm -f *.iteg

