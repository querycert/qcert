PDF2SVG=pdf2svg

all: figure.pdf figure.svg figure.png

%.svg: %.pdf
	$(PDF2SVG) $< $@

%.png: %.pdf
	convert $< $@

%.pdf: %.tex compiler-coq.tex
	pdflatex --shell-escape $<
	pdflatex --shell-escape $<
	pdflatex --shell-escape $<

clean:
	rm -f figure.out figure.log figure.aux

cleanall: clean
	rm -f *~ figure.pdf figure.png figure.svg
