# This Makefile assumes that coq already has access to
# Flocq, Interval, CompCert, etc.,
# which will be true if coq was installed through opam 
# or as a "Coq Platform" package.

COQC=coqc
COQDEP=coqdep
COQFLAGS := $(shell cat _CoqProject)

target:  vcfloat2 tests

tests: ../Test/Test.vo ../Test/TestPaper.vo ../Test/Test2.vo ../Test/summation.vo ../Test/autobisect.vo

# the vcfloat2 target is the core VCFloat tool for VCFloat2 users who don't need
# CompCert-based reification
vcfloat2:  VCFloat.vo FPCompCert.vo Version.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

ifdef INSTALLDIR
INSTALLFILES=$(shell make -Bn vcfloat2 2>/dev/null | awk '/^coqc.*v$$/{print $$NF"o"}')
endif

install: vcfloat2
ifndef INSTALLDIR
# all the "realpath" complexity in the next line is to make it work on cygwin as well as regular unix
	$(info Perhaps you mean: make install INSTALLDIR=$(shell realpath `coqc -where` | tr -d [:space:])/user-contrib/vcfloat)
	$(error INSTALLDIR must be set, for make install)
endif
	install -d $(INSTALLDIR)
	install -m 0644 $(INSTALLFILES) $(INSTALLDIR)

depend: 
	$(COQDEP) $(COQFLAGS) *.v cverif/*.v ../Test/*.v > .depend

all_clean:
	rm *.vo *.vok *.vos *.glob

-include .depend

clean:
	rm -f {*,*/*}.{vo,vo?,glob}
