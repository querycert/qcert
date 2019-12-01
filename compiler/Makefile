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

# User-level configuration
include ../Makefile.config
# Contains the list of all the Coq modules
include ../Makefile.coq_modules

## Configuraton
QCERT_HOME=$(CURDIR)/..

## Mains
MAIN=qcert
MAIN2=qdata
MAIN3=qcertJS

NATIVE=exe
BYTECODE=bc
JS=js

## Toplevel
all: ../bin/$(MAIN) ../bin/$(MAIN2) ../bin/$(MAIN3).js

native: ../bin/$(MAIN) ../bin/$(MAIN2) 

js: ../bin/$(MAIN3).js

## Extraction
VO_FILES = $(MODULES:%=./src/%.vo)

../runtimes/javascript/qcert_runtime.ml:
	$(MAKE) -C ../runtimes/javascript

utils/QcertJsRuntime.ml: ../runtimes/javascript/qcert_runtime.ml
	cp ../runtimes/javascript/qcert_runtime.ml utils/QcertJsRuntime.ml

lib/StaticConfig.ml extraction/QcertCompiler.ml extraction/QcertCompiler.mli: $(VO_FILES)
	echo "(* This file is generated *)" > lib/StaticConfig.ml
	echo "let qcert_home = \"$(QCERT_HOME)\"" >> lib/StaticConfig.ml
	(cd extraction; coqc -R ../src Qcert ./QcertExtraction.v)

## Native
../bin/$(MAIN): utils/QcertJsRuntime.ml extraction/QcertCompiler.ml extraction/QcertCompiler.mli
	cd $(QCERT_HOME)/clis/ocaml ; dune build $(MAIN).$(NATIVE)
	cp $(QCERT_HOME)/_build/default/clis/ocaml/$(MAIN).$(NATIVE) ../bin/$(MAIN)

../bin/$(MAIN2): utils/QcertJsRuntime.ml extraction/QcertCompiler.ml extraction/QcertCompiler.mli
	cd $(QCERT_HOME)/clis/ocaml ; dune build $(MAIN2).$(NATIVE)
	cp $(QCERT_HOME)/_build/default/clis/ocaml/$(MAIN2).$(NATIVE) ../bin/$(MAIN2)

## JavaScript
../bin/$(MAIN3).js: utils/QcertJsRuntime.ml extraction/QcertCompiler.ml extraction/QcertCompiler.mli
	cd $(QCERT_HOME)/compiler/libjs ; dune build $(MAIN3).$(BYTECODE)
	js_of_ocaml $(QCERT_HOME)/_build/default/compiler/libjs/$(MAIN3).$(BYTECODE)
	cp $(QCERT_HOME)/_build/default/compiler/libjs/$(MAIN3).$(JS) ../bin/$(MAIN3).$(JS)

## Clean

clean:
	ocamlbuild -clean -no-log
	rm -rf $(QCERT_HOME)/_build
	rm -f ../bin/$(MAIN)
	rm -f ../bin/$(MAIN2)
	rm -f ../bin/$(MAIN3).js

cleanall: clean
	rm -rf utils/QcertJsRuntime.ml
	rm -f extraction/QcertExtraction.glob extraction/QcertExtraction.vo extraction/.QcertExtraction.aux
	rm -rf extraction/QcertCompiler.ml extraction/QcertCompiler.mli
	rm -rf lib/StaticConfig.ml
	rm -rf *~

.NOTPARALLEL: 

