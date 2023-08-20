UNIT=40pt
GDIR = .
GEN = $(GDIR)/ddgen.py
SCALE=50pt

tex: eg4.tex 

eg4.tex: eg4.dd
	$(GEN) -i eg4.dd -o eg4.tex -u $(SCALE)

clean:
	rm -f *.tex *.pdf *~ *.log *.aux

