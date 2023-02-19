INTERP=python3
DGEN = $(INTERP) ../tools/gen-data.py
LDATA = ../benchmarks/mc2022/logs
SRCDATA = data-raw



rdata:
	cp -p $(LDATA)/time+defining.csv $(SRCDATA)
	cp -p $(LDATA)/time+defining-success.csv $(SRCDATA)
	cp -p $(LDATA)/time+defining-failure.csv $(SRCDATA)
	cp -p $(LDATA)/time-d4-verify.csv $(SRCDATA)
	cp -p $(LDATA)/defining+total.csv $(SRCDATA)
	cp -p $(LDATA)/times.csv $(SRCDATA)

data:
	rm -rf data-formatted
	mkdir data-formatted
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*, mark options={scale=0.9}, thick" \
		< $(SRCDATA)/time+defining.csv > data-formatted/time+defining.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=midblue, mark=*, mark options={scale=0.9}, thick" \
		< $(SRCDATA)/time+defining-success.csv > data-formatted/time+defining-success.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=square*, mark options={scale=0.9}, thick" \
		< $(SRCDATA)/time+defining-failure.csv > data-formatted/time+defining-failure.tex
	$(DGEN) -X 2 -Y 5 -O "only marks, color=redorange, mark=*,  mark options={scale=1.0}, thick" \
		< $(SRCDATA)/time-d4-verify.csv > data-formatted/time-d4-verify.tex
	$(DGEN) -X 2 -Y 3 -O "only marks, color=redorange, mark=*,  mark options={scale=1.0}, thick" \
		< $(SRCDATA)/defining+total.csv > data-formatted/defining+total.tex
