UNIT=40pt
GDIR = .
GEN = $(GDIR)/ddgen.py
SCALE=50pt

tex: eg4.tex eg4-slides.tex eg4-eval.tex eg4-partial.tex \
	eg-proj.tex eg-preproj.tex eg-proj-skolemize.tex

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

p2-cdcl.tex: p2-cdcl.dd
	$(GEN) -i p2-cdcl.dd -o p2-cdcl.tex -u $(SCALE)

p2-cdcl-eval.tex: p2-cdcl-eval.dd
	$(GEN) -i p2-cdcl-eval.dd -o p2-cdcl-eval.tex -u $(SCALE)

p2-cdcl-doc.pdf: p2-cdcl.dd
	$(GEN) -w -i p2-cdcl.dd -o p2-cdcl-doc.tex -u $(SCALE)
	pdflatex p2-cdcl-doc.tex

p2-cdcl-eval-doc.pdf: p2-cdcl-eval.dd
	$(GEN) -w -i p2-cdcl-eval.dd -o p2-cdcl-eval-doc.tex -u $(SCALE)
	pdflatex p2-cdcl-eval-doc.tex

eg4.tex: eg4.dd
	$(GEN) -i eg4.dd -o eg4.tex -u $(SCALE)

eg4-slides.tex: eg4-slides.dd
	$(GEN) -i eg4-slides.dd -o eg4-slides.tex -u $(UNIT) -s 0.9 -S c

eg4-eval.tex: eg4-eval.dd
	$(GEN) -i eg4-eval.dd -o eg4-eval.tex -u $(UNIT) -s 0.9 -S c

eg4-partial.tex: eg4-partial.dd
	$(GEN) -i eg4-partial.dd -o eg4-partial.tex -u $(UNIT) -s 0.9 -S c

eg4-doc.pdf: eg4.dd
	$(GEN) -w -i eg4.dd -o eg4-doc.tex -u $(SCALE)
	pdflatex eg4-doc.tex

eg4-eval-doc.pdf: eg4-eval.dd
	$(GEN) -w -i eg4-eval.dd -o eg4-eval-doc.tex -u $(SCALE)
	pdflatex eg4-eval-doc.tex

eg-proj.tex: eg-proj.dd
	$(GEN) -i eg-proj.dd -o eg-proj.tex -u $(SCALE)

eg-proj-doc.pdf: eg-proj.dd
	$(GEN) -w -i eg-proj.dd -o eg-proj-doc.tex -u $(SCALE)
	pdflatex eg-proj-doc.tex

eg-preproj.tex: eg-preproj.dd
	$(GEN) -i eg-preproj.dd -o eg-preproj.tex -u $(SCALE)

eg-preproj-doc.pdf: eg-preproj.dd
	$(GEN) -w -i eg-preproj.dd -o eg-preproj-doc.tex -u $(SCALE)
	pdflatex eg-preproj-doc.tex

eg-proj-skolemize.tex: eg-proj-skolemize.dd
	$(GEN) -i eg-proj-skolemize.dd -o eg-proj-skolemize.tex -u $(SCALE)

eg-proj-skolemize-doc.pdf: eg-proj-skolemize.dd
	$(GEN) -w -i eg-proj-skolemize.dd -o eg-proj-skolemize-doc.tex -u $(SCALE)
	pdflatex eg-proj-skolemize-doc.tex



clean:
	rm -f *.tex *.pdf *~ *.log *.aux

