PYTHON ?= python3

.PHONY: all check clean
all: check
check:
	$(PYTHON) scripts/check.py
clean:
	$(PYTHON) scripts/clean.py
