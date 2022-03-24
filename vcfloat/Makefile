# This Makefile assumes that coq already has access to
# Flocq, Interval, CompCert, etc.,
# which will be true if coq was installed through opam 
# or as a "Coq Platform" package.

COQC=coqc
COQDEP=coqdep
COQPROJECT != cat _CoqProject
COQFLAGS=$(COQPROJECT)

target: Test.vo Clight2FPOpt.vo Prune.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v cverif/*.v > .depend

include .depend

