#
# Copyright 2015-2016 IBM Corporation
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

## Configuratin for the separate ocamljava compiler
OCAMLJAVA=/Users/js/.opam/ocamljava-2.0-alpha3

###### Shouldn't have to be changed after this
OCAMLBUILD= ocamlbuild \
		-no-links -classic-display \
		-tags annot -libs str

OCAMLBUILDJAR= $(OCAMLJAVA)/bin/ocamlbuild \
		-no-links -classic-display \
		-tags annot -libs str

OCAMLWRAP=$(OCAMLJAVA)/bin/ocamlwrap

MENHIRFLAG=-use-menhir
#MENHIRFLAG=

MAIN=CACo
MAIN2=CAEv
MAIN3=CADa
TARGET=native
JAR=jar

LIB=CALib
LIBJS=CALibJS

all: $(MAIN) $(MAIN2) $(MAIN3)
jars: $(MAIN).$(JAR) $(MAIN2).$(JAR) $(MAIN3).$(JAR) $(LIB).jar

# Extraction from Coq
generated:
	mkdir -p generated
	(cd generated; coqc -R ../../coq QCert ../Extraction.v)

# OCaml build
$(MAIN): $(MAIN).$(TARGET)
	cp _build/$(MAIN).$(TARGET) $(MAIN)

$(MAIN).$(TARGET): generated
	$(OCAMLBUILD) $(MENHIRFLAG) -Is generated -Is src $(MAIN).$(TARGET)

$(MAIN).$(JAR): generated
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(MAIN).$(JAR)
	cp _build/$(MAIN).$(JAR) $(MAIN).$(JAR)

$(MAIN2): $(MAIN2).$(TARGET)
	cp _build/$(MAIN2).$(TARGET) $(MAIN2)

$(MAIN2).$(TARGET): generated
	$(OCAMLBUILD) $(MENHIRFLAG) -Is generated -Is src $(MAIN2).$(TARGET)

$(MAIN2).$(JAR): generated
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(MAIN2).$(JAR)
	cp _build/$(MAIN2).$(JAR) $(MAIN2).$(JAR)

$(MAIN3): $(MAIN3).$(TARGET)
	cp _build/$(MAIN3).$(TARGET) $(MAIN3)

$(MAIN3).$(TARGET): generated
	$(OCAMLBUILD) $(MENHIRFLAG) -Is generated -Is src $(MAIN3).$(TARGET)

$(MAIN3).$(JAR): generated
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(MAIN3).$(JAR)
	cp _build/$(MAIN3).$(JAR) $(MAIN3).$(JAR)

$(LIBJS).cma: generated
	$(OCAMLBUILD) -libs js_of_ocaml -pp "camlp4o -I /Users/simeon/.opam/4.02.1/lib/js_of_ocaml pa_js.cmo" \
        -pkg js_of_ocaml -Is generated -Is src $(LIBJS).cma
	cp _build/$(LIBJS).cma jsapi/$(LIBJS).cma

$(LIB).jar: generated
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(LIB).jar
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(LIB).cmi
	cp _build/$(LIB).jar $(LIB).jar
	cp _build/$(LIB).cmi $(LIB).cmi

# Java API

japi: japi/lib/$(LIB).jar _build/$(LIB).cmi
	cd _build ; $(OCAMLWRAP) -package "org.qcert.calib" CALib.cmi
	cp _build/CALibWrapper.java japi/src/org/qcert/calib
	$(MAKE) -C japi all

japi/lib/$(LIB).jar: $(LIB).jar
	mkdir -p japi/lib
	cp $(LIB).jar japi/lib/$(LIB).jar

# Cleanup
clean:
	ocamlbuild -clean
	rm -rf _build
	rm -f $(MAIN).$(JAR) $(MAIN2).$(JAR) $(MAIN3).$(JAR)
	rm -f $(LIB).cma $(LIB).jar $(LIB).cmi
	rm -f japi/lib/CALib.jar
	rm -f japi/src/org/qcert/calib/CALibWrapper.java
	$(MAKE) -C japi clean
	rm -f *.class
	rm -rf java

realclean:
	$(MAKE) clean
	rm -f RuleLexer.ml RuleParser.ml RuleParser.mli
	rm -f CampLexer.ml CampParser.ml CampParser.mli
	rm -f DataLexer.ml DataParser.ml DataParser.mli
	rm -f SexpLexer.ml SexpParser.ml SexpParser.mli
	rm -f Extraction.glob Extraction.vo .Extraction.aux
	rm -rf *~ generated $(MAIN) $(MAIN2) $(MAIN3)

cleanall: realclean
