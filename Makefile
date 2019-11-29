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
include Makefile.config
# Contains the list of all the Coq modules
include Makefile.coq_modules

#
CP=cp

FILES = $(addprefix compiler/src/,$(MODULES:%=%.v))

## Compiler
all: 
	@$(MAKE) qcert
	@$(MAKE) MAKEFLAGS= qcert-parser
	@$(MAKE) MAKEFLAGS= qcert-runtimes
	@$(MAKE) MAKEFLAGS= qcert-clis

# Regenerate the npm directory
npm:
	@echo "Updating npm package"
	@$(MAKE) -C npm package

qcert: Makefile.coq
	@$(MAKE) qcert-coq
	@$(MAKE) MAKEFLAGS= qcert-ocaml
	@$(MAKE) MAKEFLAGS= qcert-javascript

qcert-coq: Makefile.coq
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Coq source"
	@echo "[Q*cert] "
	@$(MAKE) -f Makefile.coq

qcert-ocaml:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to OCaml"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/extraction native

qcert-javascript:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to JavaScript"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/extraction js

qcert-parser:
	@echo "[Q*cert] "
	@echo "[Q*cert] PARSERS"
	@echo "[Q*cert] "
ifneq ($(SQL),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling SQL parser"
	@echo "[Q*cert] "
	@$(MAKE) -C parsers/sqlParser
endif
ifneq ($(SQLPP),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling SQL++ parser"
	@echo "[Q*cert] "
	@$(MAKE) -C parsers/sqlppParser
endif
ifneq ($(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling ODM rules parsers"
	@echo "[Q*cert] "
	@$(MAKE) -C parsers/jrulesParser
endif
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Installing frontend service"
	@echo "[Q*cert] "
	@$(MAKE) -C parsers/javaService all install
endif

clean-coq:
	- @$(MAKE) -f Makefile.coq clean

cleanall-coq: clean-coq

clean-ocaml:
	- @$(MAKE) -C compiler/extraction clean

cleanall-ocaml:
	- @$(MAKE) -C compiler/extraction cleanall

clean-parsers:
	- @$(MAKE) -C parsers/javaService clean
	- @$(MAKE) -C parsers/sqlParser clean
	- @$(MAKE) -C parsers/sqlppParser clean
	- @$(MAKE) -C parsers/jrulesParser clean
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar

cleanall-parsers:
	- @$(MAKE) -C parsers/javaService cleanall
	- @$(MAKE) -C parsers/sqlParser cleanall
	- @$(MAKE) -C parsers/sqlppParser cleanall
	- @$(MAKE) -C parsers/jrulesParser cleanall
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar


## Runtimes
qcert-runtimes:
	@$(MAKE) javascript-runtime
ifneq ($(JAVA),)
	@$(MAKE) java-runtime
endif
ifneq ($(SPARK),)
	@$(MAKE) spark2-runtime
endif

javascript-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building JavaScript runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtimes/javascript

java-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Java runtime"
	@echo "[Q*cert] "
	@$(MAKE) -C runtimes/java

spark2-runtime:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Spark2 runtime"
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

## CLIS
qcert-clis:
	@$(MAKE) javascript-cli
ifneq ($(JAVA),)
	@$(MAKE) java-cli
endif

javascript-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building JavaScript CLI"
	@echo "[Q*cert] "
	@$(MAKE) -C clis/nodejs all

java-cli:
	@echo "[Q*cert] "
	@echo "[Q*cert] Building Java CLI"
	@echo "[Q*cert] "
	@$(MAKE) -C clis/java all install

clean-clis:
	- @$(MAKE) -C clis/java clean
	- @rm -f bin/javaRunner.jar

cleanall-clis:
	- @$(MAKE) -C clis/java cleanall
	- @rm -f bin/javaRunner.jar

## Demo
bin/qcertJS.js:
	@$(MAKE) qcert-javascript

runtimes/javascript/qcert-runtime.js:
	@$(MAKE) javascript-runtime

demo:
	@$(MAKE) qcert-demo

qcert-demo: bin/qcertJS.js runtimes/javascript/qcert-runtime.js
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Web Demo in TypeScript"
	@echo "[Q*cert] "
	cd doc/demo && npm install && npm run compile

clean-demo:
	- @rm -f doc/demo/demo.js doc/demo/demo.js.map

cleanall-demo: clean-demo
	- @rm -rf doc/demo/node_modules

## Test

tests:
	@$(MAKE) -C test

clean-tests:
	@$(MAKE) -C test clean

cleanall-tests: clean-tests

## Install

install-coq:
	@$(MAKE) -f Makefile.coq install

## Documentation
documentation:
	@$(MAKE) -C compiler/src documentation


## Cleanup
clean: Makefile.coq remove_all_derived
	- @$(MAKE) clean-coq
	- @$(MAKE) clean-ocaml
	- @$(MAKE) clean-runtimes
	- @$(MAKE) clean-clis
	- @$(MAKE) cleanall-parsers
	- @$(MAKE) clean-demo
	- @$(MAKE) clean-tests
	- @rm -f Makefile.coq
	- @rm -f *~

cleanall: Makefile.coq remove_all_derived
	- @$(MAKE) cleanall-coq
	- @$(MAKE) cleanall-ocaml
	- @$(MAKE) cleanall-runtimes
	- @$(MAKE) cleanall-clis
	- @$(MAKE) cleanall-parsers
	- @$(MAKE) cleanall-demo
	- @$(MAKE) cleanall-tests
	- @rm -f Makefile.coq
	- @rm -f *~

cleannotall: Makefile.coq
	- @$(MAKE) cleanall-ocaml
	- @$(MAKE) cleanall-runtimes
	- @$(MAKE) cleanall-clis
	- @$(MAKE) cleanall-parsers
	- @$(MAKE) cleanall-demo
	- @$(MAKE) cleanall-tests
	- @rm -f Makefile.coq
	- @rm -f *~

clean_detritus:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 ./scripts/remove_detritus_derived_file.sh

remove_all_derived:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 rm -f

##
Makefile.coq: Makefile Makefile.coq_modules $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean clean_detritus documentation documentation_old npm qcert

