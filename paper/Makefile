LATEX ?= pdflatex
BIBTEX ?= bibtex
PYTHON ?= python3

.PHONY: all check clean
all:
	$(PYTHON) build.py --latex "$(LATEX)" --bibtex "$(BIBTEX)"

check:
	$(PYTHON) ../checks/verify_sample_hulls.py
	$(PYTHON) ../checks/verify_sampling_mass.py

clean:
	rm -f *.aux *.blg *.log *.out *.vtc *.fls *.fdb_latexmk build.log
