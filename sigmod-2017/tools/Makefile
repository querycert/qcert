OCAMLBUILD= ocamlbuild \
		-no-links -classic-display \
		-tags annot,debug
TARGET=native

all: analytics jsonpp time_n

.PHONY: analytics.$(TARGET) jsonpp.$(TARGET) time_n.$(TARGET) clean cleanall

analytics: analytics.$(TARGET)
	cp _build/$< $@

analytics.$(TARGET):
	$(OCAMLBUILD) -use-ocamlfind -pkg yojson $@

jsonpp: jsonpp.$(TARGET)
	cp _build/$< $@

jsonpp.$(TARGET):
	$(OCAMLBUILD) -use-ocamlfind -pkg yojson $@

time_n: time_n.$(TARGET)
	cp _build/$< $@

time_n.$(TARGET):
	$(OCAMLBUILD) -use-ocamlfind -lib unix $@

clean:
	$(OCAMLBUILD) -clean

cleanall: clean
	rm -f *~
	rm -f analytics jsonpp time_n
