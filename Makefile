PY ?= python3
export PYTHONPATH := src

.PHONY: test gallery theory clean

test: ; $(PY) -m pytest -q
gallery: ; $(PY) examples/build_gallery.py
theory: ; cd docs/theory && latexmk -pdf -interaction=nonstopmode main.tex
clean: ; rm -rf build dist src/*.egg-info .pytest_cache && find . -name __pycache__ -prune -exec rm -rf {} + && cd docs/theory && latexmk -c
