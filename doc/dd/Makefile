GDIR = .
GEN = $(GDIR)/ddgen.py
SCALE=50pt

c3.tex: c3.dd
	$(GEN) -i c3.dd -o c3.tex -u $(SCALE)

c3-doc.pdf: c3.dd
	$(GEN) -w -i c3.dd -o c3-doc.tex -u $(SCALE)
	pdflatex c3-doc.tex

