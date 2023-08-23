UNIT=40pt
GDIR = .
GEN = $(GDIR)/ddgen.py
SCALE=50pt

tex: eg4.tex  sdd.tex

eg4.tex: eg4.dd
	$(GEN) -i eg4.dd -o eg4.tex -u $(SCALE)

sdd.tex: sdd.dd
	$(GEN) -i sdd.dd -o sdd.tex -u $(SCALE)

sdd-doc.pdf: sdd.dd
	$(GEN) -w -i sdd.dd -o sdd-doc.tex -u $(SCALE)
	pdflatex sdd-doc.tex

clean:
	rm -f *.tex *.pdf *~ *.log *.aux

