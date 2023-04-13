COQC=coqc
COQDEP=coqdep
VCFLOAT_LOC=../vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat

all: _CoqProject target

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

target: summation.vo

%.vo: %.v 
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v > .depend

all_clean: rm *.vo *.vok *.vos *.glob

-include .depend


vcfloat: $(VCFLOAT_LOC)/Automate.vo $(VCFLOAT_LOC)/Prune.vo
	cd ../vcfloat; make vcfloat2
