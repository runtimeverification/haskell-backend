include ../include.mk

SIMPLIFICATION = $(HS_TOP)/src/Kore/Step/Simplification

Simplification.pdf: \
	$(SIMPLIFICATION)/Simplification.tex \
	$(SIMPLIFICATION)/Or.lhs
	cd "$(SIMPLIFICATION)"; \
	lualatex --output-directory=$(TOP)/docs Simplification.tex; \
	lualatex --output-directory=$(TOP)/docs Simplification.tex;
