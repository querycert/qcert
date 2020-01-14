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
include Makefile.config
# Contains the list of all the Coq modules
include Makefile.coq_modules

#
CP=cp

FILES = $(addprefix compiler/core/,$(MODULES:%=%.v))

## Full run
all:
	@$(MAKE) build
	@$(MAKE) install-local

build: 
	@$(MAKE) qcert-compiler
	@$(MAKE) MAKEFLAGS= qcert-runtimes
	@$(MAKE) MAKEFLAGS= qcert-clis

clean: Makefile.coq remove_all_derived
	- @$(MAKE) clean-qcert-compiler
	- @$(MAKE) clean-runtimes
	- @$(MAKE) clean-clis
	- @$(MAKE) clean-demo
	- @$(MAKE) clean-test
	- @rm -f Makefile.coq
	- @rm -f *~

cleanmost: Makefile.coq
	- @$(MAKE) cleanmost-qcert-compiler
	- @$(MAKE) cleanall-runtimes
	- @$(MAKE) cleanall-clis
	- @$(MAKE) cleanall-demo
	- @$(MAKE) cleanall-test
	- @rm -f Makefile.coq
	- @rm -f *~

cleanall: Makefile.coq remove_all_derived
	- @$(MAKE) cleanall-qcert-compiler
	- @$(MAKE) cleanmost


## Install

install-coqdev:
	@$(MAKE) -f Makefile.coq install

install-local: 
	@$(MAKE) install-ocaml
ifneq ($(JAVASCRIPT),)
	@$(MAKE) install-javascript
endif

install-ocaml:
	@$(MAKE) -C clis/ocaml install

install-javascript:
	@$(MAKE) -C clis/nodejs install

## Opam

coq-qcert:
	@$(MAKE) qcert-coq
	@$(MAKE) qcert-ocaml-extract


## Coq build

qcert-compiler:
	@$(MAKE) configure
	@$(MAKE) qcert-coq
	@$(MAKE) MAKEFLAGS= qcert-ocaml
ifneq ($(JAVASCRIPT),)
	@$(MAKE) MAKEFLAGS= qcert-javascript
endif
ifneq ($(JAVA),)
	@$(MAKE) MAKEFLAGS= qcert-parsersJava
endif

clean-qcert-compiler:
	- @$(MAKE) clean-configure
	- @$(MAKE) clean-qcert-coq
	- @$(MAKE) clean-qcert-ocaml
	- @$(MAKE) clean-parsersJava

cleanall-qcert-compiler:
	- @$(MAKE) cleanall-configure
	- @$(MAKE) cleanall-qcert-coq
	- @$(MAKE) cleanall-qcert-ocaml
	- @$(MAKE) cleanall-parsersJava

cleanmost-qcert-compiler:
	- @$(MAKE) cleanall-configure
	- @$(MAKE) cleanall-qcert-ocaml
	- @$(MAKE) cleanmost-parsersJava


## Configure

./runtimes/javascript/qcert_runtime.ml:
	$(MAKE) -C ./runtimes/javascript

./compiler/lib/js_runtime.ml: ./runtimes/javascript/qcert_runtime.ml
	cp ./runtimes/javascript/qcert_runtime.ml ./compiler/lib/js_runtime.ml

./compiler/lib/static_config.ml:
	echo "(* This file is generated *)" > ./compiler/lib/static_config.ml
	echo "let qcert_home = \"$(CURDIR)\"" >> ./compiler/lib/static_config.ml

prepare: ./compiler/lib/js_runtime.ml ./compiler/lib/static_config.ml Makefile.coq

configure:
	@echo "[Q*cert] "
	@echo "[Q*cert] Configuring Build"
	@echo "[Q*cert] "
	@$(MAKE) prepare

clean-configure:

cleanall-configure:
	$(MAKE) -C ./runtimes/javascript cleanall
	rm -rf ./compiler/lib/js_runtime.ml
	rm -rf ./compiler/lib/static_config.ml
	rm -f ./compiler/.merlin compiler/*/.merlin

## Compiler Core

qcert-coq: Makefile.coq
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Compiler from Coq"
	@echo "[Q*cert] "
	@$(MAKE) -f Makefile.coq

clean-qcert-coq:
	- @$(MAKE) -f Makefile.coq clean

cleanall-qcert-coq: clean-qcert-coq

### OCaml Extraction

qcert-ocaml-extract:
	@$(MAKE) -C compiler/extraction

qcert-ocaml:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting Compiler to OCaml"
	@echo "[Q*cert] "
	@$(MAKE) qcert-ocaml-extract
	dune build @install

clean-qcert-ocaml:
	- @$(MAKE) -C compiler/extraction clean
	- dune clean

cleanall-qcert-ocaml:
	- @$(MAKE) -C compiler/extraction cleanall
	- dune clean
	- rm -f *.install

### JavaScript Extraction

qcert-javascript:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting Compiler to JavaScript"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/libjs


## Java Parsers

qcert-parsersJava:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Java Parsers"
	@echo "[Q*cert] "
ifneq ($(SQL),)
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL Parser"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsersJava/sqlParser
endif
ifneq ($(SQLPP),)
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL++ Parser"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsersJava/sqlppParser
endif
ifneq ($(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM Rules Parsers"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsersJava/jrulesParser
endif
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Installing Parser Service"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsersJava/javaService all install
endif

clean-parsersJava:
	- @$(MAKE) -C compiler/parsersJava/javaService clean
	- @$(MAKE) -C compiler/parsersJava/sqlParser clean
	- @$(MAKE) -C compiler/parsersJava/sqlppParser clean
	- @$(MAKE) -C compiler/parsersJava/jrulesParser clean
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar

cleanall-parsersJava:
	- @$(MAKE) -C compiler/parsersJava/javaService cleanall
	- @$(MAKE) -C compiler/parsersJava/sqlParser cleanall
	- @$(MAKE) -C compiler/parsersJava/sqlppParser cleanall
	- @$(MAKE) -C compiler/parsersJava/jrulesParser cleanall
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar

cleanmost-parsersJava:
	- @$(MAKE) -C compiler/parsersJava/javaService cleanmost
	- @$(MAKE) -C compiler/parsersJava/sqlParser cleanmost
	- @$(MAKE) -C compiler/parsersJava/sqlppParser cleanmost
	- @$(MAKE) -C compiler/parsersJava/jrulesParser cleanmost
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar


## Runtimes
qcert-runtimes:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building runtimes"
	@echo "[Q*cert] "
ifneq ($(JAVASCRIPT),)
	@$(MAKE) javascript-runtime
endif
ifneq ($(JAVA),)
	@$(MAKE) java-runtime
endif
ifneq ($(SPARK),)
	@$(MAKE) spark2-runtime
endif

javascript-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] JavaScript runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtimes/javascript

java-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Java runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtimes/java

spark2-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Spark2 runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtimes/spark2

clean-runtimes:
	- @$(MAKE) -C runtimes/javascript clean
	- @$(MAKE) -C runtimes/java clean
	- @$(MAKE) -C runtimes/spark2 clean
	- @rm -rf bin/lib
	- @rm -f bin/javaRunner.jar

cleanall-runtimes:
	- @$(MAKE) -C runtimes/javascript cleanall
	- @$(MAKE) -C runtimes/java cleanall
	- @$(MAKE) -C runtimes/spark2 cleanall
	- @rm -rf bin/lib
	- @rm -f bin/javaRunner.jar


## CLIs
qcert-clis:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building CLIs"
	@echo "[Q*cert] "
	@$(MAKE) ocaml-cli
ifneq ($(JAVASCRIPT),)
	@$(MAKE) javascript-cli
endif
ifneq ($(JAVA),)
	@$(MAKE) java-cli
endif

ocaml-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] OCaml CLI"
	@echo "[Q*cert] "
	@$(MAKE) -C clis/ocaml all

javascript-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] Node.js CLI"
	@echo "[Q*cert] "
	@$(MAKE) -C clis/nodejs all

java-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] Java CLI"
	@echo "[Q*cert] "
	@$(MAKE) -C clis/java all install

clean-clis:
	- @$(MAKE) -C clis/ocaml clean
	- @$(MAKE) -C clis/nodejs clean
	- @$(MAKE) -C clis/java clean
	- @rm -f bin/javaRunner.jar

cleanall-clis:
	- @$(MAKE) -C clis/ocaml cleanall
	- @$(MAKE) -C clis/nodejs cleanall
	- @$(MAKE) -C clis/java cleanall
	- @rm -f bin/javaRunner.jar


## Demo
demo:
	@$(MAKE) qcert-demo

bin/qcertJS.js:
	@$(MAKE) qcert-javascript

runtimes/javascript/qcert-runtime.js:
	@$(MAKE) javascript-runtime

qcert-demo: bin/qcertJS.js runtimes/javascript/qcert-runtime.js
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Web Demo in TypeScript"
	@echo "[Q*cert] "
	cd documentation/demo && npm install && npm run compile

clean-demo:
	- @rm -f documentation/demo/demo.js documentation/demo/demo.js.map

cleanall-demo: clean-demo
	- @rm -rf documentation/demo/node_modules


## Tests

test:
	@$(MAKE) -C tests

clean-test:
	@$(MAKE) -C tests clean

cleanall-test: clean-test


## Documentation
docs:
	@$(MAKE) -C compiler/core documentation

## Misc

clean_detritus:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 ./scripts/remove_detritus_derived_file.sh

remove_all_derived:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 rm -f

Makefile.coq: Makefile Makefile.coq_modules $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean clean_detritus documentation documentation_old npm qcert

