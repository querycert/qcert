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
	@$(MAKE) MAKEFLAGS= qcert-runtimes
	@$(MAKE) qcert-compiler
	@$(MAKE) MAKEFLAGS= qcert-cli

clean: Makefile.coq remove_all_derived
	- @$(MAKE) clean-qcert-compiler
	- @$(MAKE) clean-runtimes
	- @$(MAKE) clean-cli
	- @$(MAKE) clean-demo
	- @$(MAKE) clean-test
	- @rm -f Makefile.coq
	- @rm -f *~

cleanmost: Makefile.coq
	- @$(MAKE) cleanmost-qcert-compiler
	- @$(MAKE) cleanall-runtimes
	- @$(MAKE) cleanall-cli
	- @$(MAKE) cleanall-demo
	- @$(MAKE) cleanall-test
	- @rm -f Makefile.coq
	- @rm -f *~

cleanall: Makefile.coq remove_all_derived
	- @$(MAKE) cleanall-runtimes
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
	@$(MAKE) -C cli/ocaml install

install-javascript:
	@$(MAKE) -C cli/nodejs install

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
	@$(MAKE) MAKEFLAGS= qcert-parsingJava
endif

clean-qcert-compiler:
	- @$(MAKE) clean-configure
	- @$(MAKE) clean-qcert-coq
	- @$(MAKE) clean-qcert-ocaml
	- @$(MAKE) clean-parsingJava

cleanall-qcert-compiler:
	- @$(MAKE) cleanall-configure
	- @$(MAKE) cleanall-qcert-coq
	- @$(MAKE) cleanall-qcert-ocaml
	- @$(MAKE) cleanall-parsingJava

cleanmost-qcert-compiler:
	- @$(MAKE) cleanall-configure
	- @$(MAKE) cleanall-qcert-ocaml
	- @$(MAKE) cleanmost-parsingJava


## Configure

compiler/lib/static_config.ml:
	echo "(* This file is generated *)" > compiler/lib/static_config.ml
	echo "let qcert_home = \"$(CURDIR)\"" >> compiler/lib/static_config.ml

prepare: compiler/lib/static_config.ml Makefile.coq

configure:
	@echo "[Q*cert] "
	@echo "[Q*cert] Configuring Build"
	@echo "[Q*cert] "
	@$(MAKE) prepare

clean-configure:

cleanall-configure:
	rm -rf compiler/lib/static_config.ml
	rm -f compiler/.merlin compiler/*/.merlin

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

qcert-ocaml:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting Compiler to OCaml"
	@echo "[Q*cert] "
	@$(MAKE) qcert-ocaml-extract
	dune build @install

qcert-ocaml-extract:
	- @$(MAKE) -C compiler/extraction

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
	@$(MAKE) -C compiler/libJS


## Java Parsers

qcert-parsingJava:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Java Parsers"
	@echo "[Q*cert] "
ifneq ($(SQL),)
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL Parser"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsingJava/sqlParser
endif
ifneq ($(SQLPP),)
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL++ Parser"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsingJava/sqlppParser
endif
ifneq ($(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM Rules Parsers"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsingJava/jrulesParser
endif
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Installing Parser Service"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsingJava/javaService all install
endif

clean-parsingJava:
	- @$(MAKE) -C compiler/parsingJava/javaService clean
	- @$(MAKE) -C compiler/parsingJava/sqlParser clean
	- @$(MAKE) -C compiler/parsingJava/sqlppParser clean
	- @$(MAKE) -C compiler/parsingJava/jrulesParser clean
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar

cleanall-parsingJava:
	- @$(MAKE) -C compiler/parsingJava/javaService cleanall
	- @$(MAKE) -C compiler/parsingJava/sqlParser cleanall
	- @$(MAKE) -C compiler/parsingJava/sqlppParser cleanall
	- @$(MAKE) -C compiler/parsingJava/jrulesParser cleanall
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar

cleanmost-parsingJava:
	- @$(MAKE) -C compiler/parsingJava/javaService cleanmost
	- @$(MAKE) -C compiler/parsingJava/sqlParser cleanmost
	- @$(MAKE) -C compiler/parsingJava/sqlppParser cleanmost
	- @$(MAKE) -C compiler/parsingJava/jrulesParser cleanmost
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar


## Runtimes
qcert-runtimes:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building runtimes"
	@echo "[Q*cert] "
ifneq ($(JAVA),)
	@$(MAKE) java-runtime
endif
ifneq ($(SPARK),)
	@$(MAKE) spark2-runtime
endif

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
	- @$(MAKE) -C runtimes/java clean
	- @$(MAKE) -C runtimes/spark2 clean
	- @rm -rf bin/lib
	- @rm -f bin/javaRunner.jar

cleanall-runtimes:
	- @$(MAKE) -C runtimes/java cleanall
	- @$(MAKE) -C runtimes/spark2 cleanall
	- @rm -rf bin/lib
	- @rm -f bin/javaRunner.jar


## CLI
qcert-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building CLI"
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
	@$(MAKE) -C cli/ocaml all

javascript-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] Node.js CLI"
	@echo "[Q*cert] "
	@$(MAKE) -C cli/nodejs all

java-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] Java CLI"
	@echo "[Q*cert] "
	@$(MAKE) -C cli/java all install

clean-cli:
	- @$(MAKE) -C cli/ocaml clean
	- @$(MAKE) -C cli/nodejs clean
	- @$(MAKE) -C cli/java clean
	- @rm -f bin/javaRunner.jar

cleanall-cli:
	- @$(MAKE) -C cli/ocaml cleanall
	- @$(MAKE) -C cli/nodejs cleanall
	- @$(MAKE) -C cli/java cleanall
	- @rm -f bin/javaRunner.jar


## Demo
demo:
	@$(MAKE) qcert-demo

bin/qcertJS.js:
	@$(MAKE) qcert-javascript

qcert-demo: bin/qcertJS.js
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
	dune runtest
	@$(MAKE) -C tests

clean-test:
	@$(MAKE) -C tests clean

cleanall-test: clean-test


## Documentation
docs:
	@$(MAKE) -C compiler/core documentation

## Misc

clean_detritus:
	@find . \( -name '*.vo' -or -name '*.vos' -or -name '*.vok' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 scripts/remove_detritus_derived_file.sh

remove_all_derived:
	@find . \( -name '*.vo' -or -name '*.vos' -or -name '*.vok' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 rm -f

Makefile.coq: Makefile Makefile.coq_modules $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean clean_detritus documentation documentation_old npm qcert

