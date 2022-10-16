COQC=coqc
COQDEP=coqdep
VCFLOAT_LOC=../vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat

all: _CoqProject univariate.vo 

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

target: univariate.vo multivar_2.vo doppler.vo 

%.vo: %.v 
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v cverif/*.v > .depend

all_clean: rm *.vo *.vok *.vos *.glob

-include .depend


vcfloat: $(VCFLOAT_LOC)/Automate.vo $(VCFLOAT_LOC)/Prune.vo
	cd ../vcfloat; make vcfloat2
