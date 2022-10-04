COQC=coqc
COQDEP=coqdep
VCFLOAT_LOC=../vcfloat
COQFLAGS= -Q $(VCFLOAT_LOC) vcfloat

all: _CoqProject vcfloat_tests_thms.vo

_CoqProject: Makefile
	echo $(COQFLAGS) >_CoqProject

vcfloat_tests.vo: vcfloat_tests.v vcfloat
	$(COQC) $(COQFLAGS) $<

vcfloat_tests_thms.vo: vcfloat_tests_thms.v
	$(COQC) $(COQFLAGS) $<


# ../vcfloat/%.vo: ../vcfloat/%.v

# ./%.vo: ./%.v
# 	$(COQC) $(COQFLAGS) $*.v

depend: .depend

.depend: 
	$(COQDEP) $(COQFLAGS) *.v > .depend

include .depend

clean:
	rm -f *.vo *.vok *.vos *.glob 

vcfloat: $(VCFLOAT_LOC)/Automate.vo $(VCFLOAT_LOC)/Prune.vo
	cd ../vcfloat; make vcfloat2
