SRCS= $(wildcard *.ps)
OBJS= $(SRCS:.ps=.pdf)

default: $(OBJS)

%.pdf : %.ps
	epstool --copy --bbox $*.ps --output $*.out.ps
	epstopdf $*.out.ps
	mv $*.out.pdf $*.pdf
	rm $*.out.ps

encoding.pdf: $(OBJS)
	pdflatex -shell-escape encoding

all: encoding.pdf