GDIR=../generators
CGEN = $(GDIR)/nqueen_cnf.py
SDIR=../../src
GITE=$(SDIR)/geniteg.py
VFLAG=-v 1
# KFLAG=-k
KFLAG=

N=08

qdo: nqueen-direct-onehot-$(N).data
qdb: nqueen-direct-binary-$(N).data

qso: nqueen-sinz-onehot-$(N).data
qsb: nqueen-sinz-binary-$(N).data



nqueen-direct-onehot-$(N).data:
	$(CGEN) -n $(N) -V o -C d -r nqueen-direct-onehot-$(N)-constraints 
	$(GITE) $(VFLAG) $(KFLAG) -i nqueen-direct-onehot-$(N)-constraints.qcnf -o nqueen-direct-onehot-$(N).iteg -P nqueen-direct-onehot-$(N)-constraints.order \
		-L nqueen-direct-onehot-$(N).data
	rm -f nqueen-direct-onehot-$(N)-constraints.qcnf nqueen-direct-onehot-$(N)-constraints.order

nqueen-direct-binary-$(N).data:
	$(CGEN) -n $(N) -V b -C d -r nqueen-direct-binary-$(N)-constraints | tee nqueen-direct-binary-$(N).data
	$(GITE) $(VFLAG) $(KFLAG) -i nqueen-direct-binary-$(N)-constraints.qcnf -o nqueen-direct-binary-$(N).iteg -P nqueen-direct-binary-$(N)-constraints.order \
		-L nqueen-direct-binary-$(N).data
	rm -f nqueen-direct-binary-$(N)-constraints.qcnf nqueen-direct-binary-$(N)-constraints.order

nqueen-sinz-onehot-$(N).data:
	$(CGEN) -n $(N) -V o -C s -r nqueen-sinz-onehot-$(N)-constraints | tee nqueen-sinz-onehot-$(N).data
	$(GITE) $(VFLAG) $(KFLAG) -i nqueen-sinz-onehot-$(N)-constraints.qcnf -o nqueen-sinz-onehot-$(N).iteg -P nqueen-sinz-onehot-$(N)-constraints.order \
		-L nqueen-sinz-onehot-$(N).data
	rm -f nqueen-sinz-onehot-$(N)-constraints.qcnf nqueen-sinz-onehot-$(N)-constraints.order

nqueen-sinz-binary-$(N).data:
	$(CGEN) -n $(N) -V b -C s -r nqueen-sinz-binary-$(N)-constraints | tee nqueen-sinz-binary-$(N).data
	$(GITE) $(VFLAG) $(KFLAG) -i nqueen-sinz-binary-$(N)-constraints.qcnf -o nqueen-sinz-binary-$(N).iteg -P nqueen-sinz-binary-$(N)-constraints.order \
		-L nqueen-sinz-binary-$(N).data
	rm -f nqueen-sinz-binary-$(N)-constraints.qcnf nqueen-sinz-binary-$(N)-constraints.order


clean:
	rm -f *.qcnf *.iteg *.qproof *.order *~

superclean: clean
	rm -f *.data

