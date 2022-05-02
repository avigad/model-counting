GDIR = .
GEN = $(GDIR)/ddgen.py
SCALE=50pt

tex: c3.tex c3-eval.tex p2-bdd.tex p2-bdd-eval.tex


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

p2-bdd.tex: p2-bdd.dd
	$(GEN) -i p2-bdd.dd -o p2-bdd.tex -u $(SCALE)

p2-bdd-eval.tex: p2-bdd-eval.dd
	$(GEN) -i p2-bdd-eval.dd -o p2-bdd-eval.tex -u $(SCALE)

p2-bdd-doc.pdf: p2-bdd.dd
	$(GEN) -w -i p2-bdd.dd -o p2-bdd-doc.tex -u $(SCALE)
	pdflatex p2-bdd-doc.tex

p2-bdd-eval-doc.pdf: p2-bdd-eval.dd
	$(GEN) -w -i p2-bdd-eval.dd -o p2-bdd-eval-doc.tex -u $(SCALE)
	pdflatex p2-bdd-eval-doc.tex

clean:
	rm -f *.tex *.pdf *~ *.log *.aux

