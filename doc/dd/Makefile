GDIR = .
GEN = $(GDIR)/ddgen.py
SCALE=50pt

tex: c3.tex c3-eval.tex p2.tex p2-eval.tex

c3.tex: c3.dd
	$(GEN) -i c3.dd -o c3.tex -u $(SCALE)

c3-eval.tex: c3-eval.dd
	$(GEN) -i c3-eval.dd -o c3-eval.tex -u $(SCALE)

c3-doc.pdf: c3.dd
	$(GEN) -w -i c3.dd -o c3-doc.tex -u $(SCALE)
	pdflatex c3-doc.tex

c3-eval-doc.pdf: c3-eval.dd
	$(GEN) -w -i c3-eval.dd -o c3-eval-doc.tex -u $(SCALE)
	pdflatex c3-eval-doc.tex

p2.tex: p2.dd
	$(GEN) -i p2.dd -o p2.tex -u $(SCALE)

p2-eval.tex: p2-eval.dd
	$(GEN) -i p2-eval.dd -o p2-eval.tex -u $(SCALE)

p2-doc.pdf: p2.dd
	$(GEN) -w -i p2.dd -o p2-doc.tex -u $(SCALE)
	pdflatex p2-doc.tex

p2-eval-doc.pdf: p2-eval.dd
	$(GEN) -w -i p2-eval.dd -o p2-eval-doc.tex -u $(SCALE)
	pdflatex p2-eval-doc.tex

