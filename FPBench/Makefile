COQC=coqc
COQDEP=coqdep
VCFLOAT_LOC=../vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat

all: _CoqProject target

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

target: doppler.vo univariate.vo multivar_2.vo multivar_6.vo jetengine.vo \
     kepler.vo rigid_body.vo turbine.vo

%.vo: %.v 
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v cverif/*.v > .depend

all_clean: rm *.vo *.vok *.vos *.glob

-include .depend


vcfloat: $(VCFLOAT_LOC)/Automate.vo $(VCFLOAT_LOC)/Prune.vo
	cd ../vcfloat; make vcfloat2
