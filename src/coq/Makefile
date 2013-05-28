COQC = coqc
COQDEP = coqdep
COQDOC = coqdoc

INCDIRS = \
	metalib \
	lib \
	.


DOCDIR = doc/html

FILES = \
	Dot_Labels \
	Dot_Syntax \
	Dot_Definitions \
	Dot_Rules \
	Dot_Lemmas \
	Dot_Transitivity \
	Dot_Theorems \

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
