COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

INCDIRS = \
	../metalib \
	../lib \
	.


DOCDIR = doc/html

FILES = \
	Dot_Labels \
	Dot_Syntax \
	Dot_Definitions \
  Dot_Rules \
	Dot_Tactics \
	Dot_Lemmas \
  Dot_Examples \
  Dot_Transitivity \
  Dot_Theorems \
  Dot_Preservation \
	Dot_Safety \
  Dot_Rules_Fool \
  Dot_Lemmas_Fool \
	Dot_Anf_Syntax \
	Dot_Anf_Definitions \
	Dot_Anf_Rules \
	Dot_Anf_Lemmas \
	Dot_Anf_Transitivity \
	Dot_Anf_Theorems \

VFILES   = $(foreach i, $(FILES), $(i).v)
VOFILES  = $(foreach i, $(FILES), $(i).vo)
INCFLAGS = $(foreach i, $(INCDIRS), -I $(i))

.SUFFIXES: .v .vo

all: coq

coq: $(VOFILES)

doc:
	+make documentation

documentation: $(DOCDIR) $(VOFILES)
	$(COQDOC) -g --quiet --noindex --html -d $(DOCDIR) $(VFILES)
	cp -f custom.css $(DOCDIR)/coqdoc.css

clean:
	rm -f *.vo *.glob *.cmi *.cmx *.o
	rm -rf $(DOCDIR)

%.vo: %.v Makefile
	$(COQC) -q $(INCFLAGS) $<

$(DOCDIR):
	mkdir -p $(DOCDIR)

.depend: $(VFILES) Makefile
	$(COQDEP) $(INCFLAGS) $(VFILES) > .depend

include .depend

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
