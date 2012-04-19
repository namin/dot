OTT_HOME = ~/local/ott_distro_0.21.2
OTT = $(OTT_HOME)/bin/ott

sanity :
	echo "OTT"
	$(OTT) -coq_expand_list_types false -i dot.ott -o dot.tex -o dot.v
	echo "COQ"
	coqc -I $(OTT_HOME)/coq dot.v

show :
	$(OTT) -show_sort true -show_defns true -i dot.ott

dot.pdf : sanity
	pdflatex dot

preservation.tex : sanity
	pandoc -s preservation.md -o preservation_md.tex
	$(OTT) -i dot.ott -o dot_defs.tex -tex_wrap false -tex_filter preservation_md.tex preservation_ott.tex
	cat dot_defs.tex preservation_ott.tex > preservation.tex

preservation.pdf : preservation.tex
	pdflatex preservation

all: dot.pdf preservation.pdf

