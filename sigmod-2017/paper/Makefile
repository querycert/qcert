# --------------------------------------------------------------------
# Usage:
#
#	all	 make pdf file
#	pdf	 make pdf file
#	clean	 remove files
#	clobber  remove everything
#	check	 doubled word and latex syntax check
#	wc	 word count
# --------------------------------------------------------------------

NAME := main
INPUT := macros.tex main.tex introduction.tex variables.tex nraenv.tex \
	optimization.tex nraenvout.tex queriesapp.tex rulesapp.tex mechanization.tex related.tex \
         conclusion.tex qcert-pipeline.pdf camp.tex
BIBFILES := main.bib

DISTILLER := ps2pdf

# --------------------------------------------------------------------

SHELL := bash
LATEX := pdflatex
BIBTEX := bibtex -min-crossrefs=100 # avoid separating out crossrefs
DETEX := detex -n
LACHECK := lacheck
DW := dw # ftp://ftp.math.utah.edu/pub/misc/dw.tar.gz
RM := rm -f
WC := wc

# --------------------------------------------------------------------

all: $(NAME).pdf
pdf: $(NAME).pdf
check: dw syn

$(NAME).pdf: $(INPUT) $(BIBFILES)
	@echo '-------------------- latex #1 --------------------'
	$(LATEX) $(NAME).tex
	@echo '-------------------- bibtex --------------------'
	$(BIBTEX) $(NAME)
	@echo '-------------------- latex #2 --------------------'
	$(LATEX) $(NAME).tex
	@echo '-------------------- latex #3 --------------------'
	$(LATEX) $(NAME).tex

dw:
	@-$(RM) $(NAME).dw
	@echo '-------------------- doubled words --------------------'
	@for f in $(NAME).tex ;\
	do \
		echo ----- $$f ----- ; \
		echo ----- $$f ----- >> $(NAME).dw ; \
		$(DETEX) $$f  | $(DW) >> $(NAME).dw ; \
	done

syn:
	@echo '-------------------- syntax check --------------------'
	@$(LACHECK) $(NAME).tex

wc:
	@$(DETEX) $(NAME).tex | $(WC)

clean:
	$(RM) *.{blg,dvi,dw,ilg,log,o,tmp,lbl,aux,bbl,vtc,idx,ind,toc,lof,lot,brf,out,synctex.gz} $(NAME).pdf

clobber: clean
	$(RM) *~ \#* core
