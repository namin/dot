fresh: 
%.pdf : fresh
	epstool --copy --bbox $*.ps --output $*.out.ps
	epstopdf $*.out.ps
	mv $*.out.pdf $*.pdf
	rm $*.out.ps
