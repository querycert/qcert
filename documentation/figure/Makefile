PDF2SVG=pdf2svg

all: figure.pdf figure.svg figure.png

%.svg.gen: %.dvi
	dvisvgm $< -o "%f.svg.gen"

node_modules:
	npm install

%.js %.js.map: %.ts node_modules
	./node_modules/.bin/tsc

%.svg: %.svg.gen figure.js
	node ./figure.js $< > $@

%.png: %.pdf
	convert $< $@

%.pdf: %.tex compiler-coq.tex tikzmacros.tex
	pdflatex --shell-escape $<
	pdflatex --shell-escape $<
	pdflatex --shell-escape $<

%.dvi: %.tex compiler-coq.tex tikzmacros.tex
	latex $<
	latex $<

clean:
	rm -f *~ figure.out figure.log figure.aux figure.dvi figure.svg.gen figure.lg figure.js figure.js.map

cleanall: clean
	rm -f figure.pdf figure.png figure.svg

cleandist: cleanall
	rm -rf node_modules

PRECIOUS: *.gen.svg *.dvi
