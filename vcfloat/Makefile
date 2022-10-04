# This Makefile assumes that coq already has access to
# Flocq, Interval, CompCert, etc.,
# which will be true if coq was installed through opam 
# or as a "Coq Platform" package.

COQC=coqc
COQDEP=coqdep
COQFLAGS := $(shell cat _CoqProject)

target: Test.vo TestPaper.vo Test2.vo FPSolve.vo Clight2FPOpt.vo Prune.vo

# the vcfloat2 target is the core VCFloat tool for VCFloat2 users who don't need
# CompCert-based reification
vcfloat2: Automate.vo Prune.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v cverif/*.v > .depend

all_clean:
	rm *.vo *.vok *.vos *.glob

-include .depend

