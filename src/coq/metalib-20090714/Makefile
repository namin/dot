############################################################################
#
#  Primary targets:
#    all           - the default target; synonym for 'coq'
#    coq           - builds all .vo files
#    doc           - synonym for 'documentation'
#    documentation - builds all html documentation
#    clean         - removes generated files
#
#  Other targets (intended to be used by the developers of this library):
#    gens          - builds generated .v files on demand
#    dist          - builds a zip file for distribution
#
############################################################################

## Paths to executables. Do not include options here.
## Modify these to suit your Coq installation, if necessary.

COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

## Include directories, one per line.

INCDIRS = \
	.

## Directory where generated HTML documentation should go.

DOCDIR = doc/html

## List of files to be compiled and documented.

FILES = \
	AssocList \
	CoqEqDec \
	CoqFSetDecide \
	CoqFSetInterface \
	CoqListFacts \
	CoqUniquenessTac \
	CoqUniquenessTacEx \
	FSetExtra \
	FSetWeakNotin \
	LibDefaultSimp \
	LibLNgen \
	LibTactics \
	\
	MetatheoryAtom \
	Metatheory \
	\
	AssumeList \
	MetatheoryAlt \
	\
	Fsub_LetSum_Definitions \
	Fsub_LetSum_Infrastructure \
	Fsub_LetSum_Lemmas \
	Fsub_LetSum_Soundness \
	\
	CoqIntro \
	STLCsol \

## Lists calculated from the above.

VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)
INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

############################################################################

.PHONY: all clean coq dist doc documentation gens
.SUFFIXES: .v .vo

all: Metatheory.vo MetatheoryAlt.vo LibLNgen.vo

coq: $(VOFILES)

doc:
	+make documentation

documentation: $(DOCDIR) $(VOFILES)
	$(COQDOC) -g --quiet --noindex --html -d $(DOCDIR) $(VFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)

############################################################################

%.vo: %.v Makefile
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

############################################################################

.depend: $(VFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend

############################################################################

DATE = $(shell date +%Y%m%d)
DIR  = metalib-$(DATE)

COQSPLIT = ../../books/sf/tools/coqsplit
STLC = ../../books/coqbook/stlc/STLC.v

gens:
	make -C ../../books/sf tools/coqsplit
	$(COQSPLIT) < $(STLC) > STLC.v
	$(COQSPLIT) -solutions < $(STLC) > STLCsol.v

dist:
	svn export . $(DIR)
	(cd $(DIR); $(MAKE) documentation)
	rm -f $(DIR)/*.vo $(DIR)/*.glob
	rm -f $(DIR)/TODO.txt
	echo Release $(DATE) / svn revision `svnversion .` >> $(DIR)/VERSION
	zip -r $(DIR).zip $(DIR)
	@echo
	@echo Done.
	@echo See $(DIR) and $(DIR).zip.
