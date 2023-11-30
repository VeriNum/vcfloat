COQC=coqc
COQDEP=coqdep
VCFLOAT_LOC=../vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat

all: _CoqProject target

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

target: doppler1.vo doppler2.vo doppler3.vo predatorprey.vo verhulst.vo carbongas.vo t_div_t1.vo\
     kepler0.vo kepler1.vo kepler2.vo rigid_body1.vo rigid_body2.vo turbine1.vo turbine2.vo\
     turbine3.vo himmilbeau.vo jetengine.vo

%.vo: %.v 
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v cverif/*.v > .depend

all_clean: rm *.vo *.vok *.vos *.glob

-include .depend


vcfloat: $(VCFLOAT_LOC)/Automate.vo $(VCFLOAT_LOC)/Prune.vo
	cd ../vcfloat; make vcfloat2
