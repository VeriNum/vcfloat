# This Makefile assumes that coq already has access to
# Flocq, Interval, CompCert, etc.,
# which will be true if coq was installed through opam 
# or as a "Coq Platform" package.

COQC=coqc
COQDEP=coqdep
COQFLAGS := $(shell cat _CoqProject)

target:  vcfloat2 tests

tests: ../Test/Test.vo ../Test/TestFunc.vo ../Test/TestPaper.vo ../Test/Test2.vo ../Test/summation.vo ../Test/autobisect.vo ../Test/Nonstd.vo

# the vcfloat2 target is the core VCFloat tool for VCFloat2 users who don't need
# CompCert-based reification
vcfloat2:  VCFloat.vo FPCompCert.vo Version.vo FPLib.vo FPStdLib.vo FPStdCompCert.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

INSTALLFILES ?= $(shell make -Bn vcfloat2 2>/dev/null | awk '/^coqc.*v$$/{print $$NF"o"}')

# all the "realpath" complexity in the next line is to make it work on cygwin as well as regular unix
INSTALLDIR ?= $(shell realpath `coqc -where` | tr -d [:space:])/user-contrib/vcfloat

install: vcfloat2
	install -d $(INSTALLDIR)
	install -m 0644 $(INSTALLFILES) $(INSTALLDIR)

depend: 
	$(COQDEP) $(COQFLAGS) *.v ../Test/*.v > .depend

ifneq ($(MAKECMDGOALS),depend)
 ifneq ($(MAKECMDGOALS),clean)
  include .depend
 endif
endif

all_clean:
	rm *.vo *.vok *.vos *.glob


clean:
	rm -f {*,*/*}.{vo,vo?,glob}
