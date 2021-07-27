# This Makefile assumes that coq already has access to
# Flocq, Interval, CompCert, etc.,
# which will be true if coq was installed through opam 
# or as a "Coq Platform" package.

COQC=coqc
COQFLAGS=

target: Test.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

depend: 
	coqdep *.v > .depend

include .depend

