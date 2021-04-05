# Translate DD's into different graph types
TDIR = ../../translate
TRANS=$(TDIR)/ddtrans.py

%.iteg : %.dd
	$(TRANS) -i $< -I $@

%.aig : %.dd
	$(TRANS) -i $< -A $@
OFILES =  a+b.c+d-bdd.iteg and2-add.iteg nor23of4-zdd.iteg or2-add.iteg or3-bdd.iteg x2of4-zdd.iteg \
	xor3-add.iteg xor3-bdd.iteg xor3-zdd.iteg xor4-bdd.iteg 

all: $(OFILES)

clean:
	rm -f *.aig *.iteg *~
