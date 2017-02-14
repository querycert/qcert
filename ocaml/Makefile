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

## CONFIGURATON
QCERT_HOME=$(CURDIR)/..

## Configuratin for the separate ocamljava compiler
OCAMLJAVA=/Users/js/.opam/ocamljava-2.0-alpha3

###### Shouldn't have to be changed after this
OCAMLBUILD= ocamlbuild \
		-no-links -classic-display \
		-tags annot -use-ocamlfind -package str -package unix -package base64

OCAMLBUILDJAR= $(OCAMLJAVA)/bin/ocamlbuild \
		-no-links -classic-display \
		-tags annot -libs str

OCAMLWRAP=$(OCAMLJAVA)/bin/ocamlwrap

MENHIRFLAG=-use-menhir
#MENHIRFLAG=

MAIN=qcert
TARGET=native
JAR=jar

LIB=CALib
LIBJS=CALibJS

all: $(MAIN)
jars: $(MAIN).$(JAR) $(LIB).jar
js: qcertJS.js

generated: generated/StaticConfig.ml generated/Compiler.ml generated/Compiler.mli

# Extraction from Coq
generated/Compiler.ml generated/Compiler.mli:
	mkdir -p generated
	(cd generated; coqc -R ../../coq Qcert ../Extraction.v)

# Configuration
generated/StaticConfig.ml:
	mkdir -p generated
	echo "(* This file is generated *)" > generated/StaticConfig.ml
	echo "let qcert_home = \"$(QCERT_HOME)\"" >> generated/StaticConfig.ml


# OCaml build
$(MAIN): generated $(MAIN).$(TARGET)
	cp _build/$(MAIN).$(TARGET) ../bin/$(MAIN)

$(MAIN).$(TARGET): generated
	$(OCAMLBUILD) $(MENHIRFLAG) -Is generated -Is src $(MAIN).$(TARGET)

$(MAIN).$(JAR): generated
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(MAIN).$(JAR)
	cp _build/$(MAIN).$(JAR) $(MAIN).$(JAR)

$(LIBJS).cma: generated
	$(OCAMLBUILD) -libs js_of_ocaml -pp "camlp4o -I /Users/simeon/.opam/4.02.1/lib/js_of_ocaml pa_js.cmo" \
        -pkg js_of_ocaml -Is generated -Is src $(LIBJS).cma
	cp _build/$(LIBJS).cma jsapi/$(LIBJS).cma

../lib/$(LIB).jar ../lib/$(LIB).cmi _build/$(LIB).cmi: generated
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(LIB).jar
	$(OCAMLBUILDJAR) $(MENHIRFLAG) -Is generated -Is src $(LIB).cmi
	cp _build/$(LIB).jar ../lib/$(LIB).jar
	cp _build/$(LIB).cmi ../lib/$(LIB).cmi

# Java API

japi: ../lib/$(LIB).jar ../lib/$(LIB).cmi _build/CALib.cmi
	cd _build ; $(OCAMLWRAP) -package "org.qcert.calib" CALib.cmi
	cp _build/CALibWrapper.java japi/src/org/qcert/calib
	$(MAKE) -C japi all

japi/lib/$(LIB).jar: $(LIB).jar
	mkdir -p japi/lib
	cp $(LIB).jar japi/lib/$(LIB).jar

# JavaScript

qcertJS.js: qcertJS.byte
	js_of_ocaml _build/qcertJS.byte
	cp _build/qcertJS.js ../lib/qcertJS.js

qcertJS.byte: generated qcertJS.ml
	$(OCAMLBUILD) $(MENHIRFLAG) -use-ocamlfind -package js_of_ocaml -package js_of_ocaml.ppx -Is generated -Is src qcertJS.byte

wsk-update:
	wsk action update qcert _build/qcertJS.js

wsk-invoke:
	wsk action invoke -v -br qcert -p source camp -p target nraenv \
		-p query pit
# -p query 'punop AFlatten (pletIt ((pgetconstant "WORLD")) (pmap (pletEnv (pletIt (pletIt (punop (ACast ["entities.Customer"]) (pit)) (pleft)) (pletEnv (punop (ARec "c") (pit)) (pletEnv (passert (pbinop AEq (pletIt (punop AUnbrand (pit)) (pletIt (punop (ADot "age") (pit)) (pit))) (#` 32))) (pletIt (penv) (pit))))) (punop AColl (pbinop ASConcat (punop AToString (#` "Customer =")) (punop AToString (pletIt (pletIt (penv) (punop (ADot "c") (pit))) (pletIt (punop AUnbrand (pit)) (pletIt (punop (ADot "name") (pit)) (pit))))))))))'

# clean

clean:
	ocamlbuild -clean -no-log
	rm -rf _build
	rm -f $(MAIN).$(JAR)
	rm -f ../$(LIB).cma ../$(LIB).jar ../$(LIB).cmi
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
	rm -rf *~ generated $(MAIN)
	rm -f ../bin/$(MAIN)
	rm -f ../lib/$(LIB).jar ../lib/$(LIB).cmi ../lib/qcertJS.js

cleanall: realclean

.NOTPARALLEL: 
