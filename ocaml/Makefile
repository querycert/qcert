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
		-tags annot -use-ocamlfind -package unix -package base64

MENHIRFLAG=-use-menhir
#MENHIRFLAG=

MAIN=qcert
MAIN2=qdata
TARGET=native

all: $(MAIN) $(MAIN2)
js: ../lib/qcertJS.js

extracted: extracted/StaticConfig.ml extracted/QcertCompiler.ml extracted/QcertCompiler.mli

# Extraction from Coq
extracted/QcertCompiler.ml extracted/QcertCompiler.mli:
	mkdir -p extracted
	(cd extracted; coqc -R ../../coq Qcert ../QcertExtraction.v)

# Configuration
extracted/StaticConfig.ml:
	mkdir -p extracted
	echo "(* This file is generated *)" > extracted/StaticConfig.ml
	echo "let qcert_home = \"$(QCERT_HOME)\"" >> extracted/StaticConfig.ml


# OCaml build
$(MAIN): extracted $(MAIN).$(TARGET)
	cp _build/$(MAIN).$(TARGET) ../bin/$(MAIN)

$(MAIN).$(TARGET): extracted
	$(OCAMLBUILD) $(MENHIRFLAG) -Is extracted -Is src $(MAIN).$(TARGET)

$(MAIN2): extracted $(MAIN2).$(TARGET)
	cp _build/$(MAIN2).$(TARGET) ../bin/$(MAIN2)

$(MAIN2).$(TARGET): extracted
	$(OCAMLBUILD) $(MENHIRFLAG) -Is extracted -Is src $(MAIN2).$(TARGET)

$(LIBJS).cma: extracted
	$(OCAMLBUILD) -libs js_of_ocaml -pp "camlp4o -I /Users/simeon/.opam/4.02.1/lib/js_of_ocaml pa_js.cmo" \
        -pkg js_of_ocaml -Is extracted -Is src $(LIBJS).cma
	cp _build/$(LIBJS).cma jsapi/$(LIBJS).cma

# JavaScript

../lib/qcertJS.js: _build/qcertJS.byte
	js_of_ocaml _build/qcertJS.byte
	cp _build/qcertJS.js ../lib/qcertJS.js

_build/qcertJS.byte: extracted qcertJS.ml
	$(OCAMLBUILD) $(MENHIRFLAG) -use-ocamlfind -package js_of_ocaml -package js_of_ocaml.ppx -Is extracted -Is src qcertJS.byte

# Whisk

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
	rm -f ../$(LIB).cma ../$(LIB).cmi
	rm -f *.class
	rm -rf java

realclean:
	$(MAKE) clean
	rm -f RuleLexer.ml RuleParser.ml RuleParser.mli
	rm -f CampLexer.ml CampParser.ml CampParser.mli
	rm -f DataLexer.ml DataParser.ml DataParser.mli
	rm -f SexpLexer.ml SexpParser.ml SexpParser.mli
	rm -f QcertExtraction.glob QcertExtraction.vo .QcertExtraction.aux
	rm -rf *~ extracted $(MAIN) $(MAIN2)
	rm -f ../bin/$(MAIN) ../bin/$(MAIN2)
	rm -f ../lib/$(LIB).cmi ../lib/qcertJS.js

cleanall: realclean

.NOTPARALLEL: 

