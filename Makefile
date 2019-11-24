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
TSC?=tsc

FILES = $(addprefix coq/,$(MODULES:%=%.v))

## Compiler
all: 
	@$(MAKE) qcert
	@$(MAKE) MAKEFLAGS= qcert-runtimes
	@$(MAKE) MAKEFLAGS= qcert-runners
	@$(MAKE) npm

# Regenerate the npm directory
npm:
	@echo "Updating npm package"
	@$(MAKE) -C npm package

qcert: Makefile.coq
	@$(MAKE) qcert-coq
	@$(MAKE) MAKEFLAGS= qcert-ocaml
	@$(MAKE) MAKEFLAGS= qcert-javascript
	@$(MAKE) MAKEFLAGS= qcert-java

qcert-coq: Makefile.coq
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Coq source"
	@echo "[Q*cert] "
	@$(MAKE) -f Makefile.coq

qcert-ocaml:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to OCaml"
	@echo "[Q*cert] "
	@$(MAKE) -C ocaml native

qcert-javascript:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to JavaScript"
	@echo "[Q*cert] "
	@$(MAKE) -C ocaml js

qcert-java:
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Java service"
	@echo "[Q*cert] "
	@$(MAKE) -C javaService
endif
ifneq ($(SQL),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling SQL parser"
	@echo "[Q*cert] "
	@$(MAKE) -C sqlParser
endif
ifneq ($(SQLPP),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling SQL++ parser"
	@echo "[Q*cert] "
	@$(MAKE) -C sqlppParser
endif
ifneq ($(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling ODM rules parsers"
	@echo "[Q*cert] "
	@$(MAKE) -C jrulesParser
endif
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Installing Java service"
	@echo "[Q*cert] "
	@$(MAKE) -C javaService install
endif

clean-coq:
	- @$(MAKE) -f Makefile.coq clean

cleanall-coq: clean-coq

clean-ocaml:
	- @$(MAKE) -C ocaml clean

cleanall-ocaml:
	- @$(MAKE) -C ocaml cleanall

clean-java:
	- @$(MAKE) -C javaService clean
	- @$(MAKE) -C sqlParser clean
	- @$(MAKE) -C sqlppParser clean
	- @$(MAKE) -C jrulesParser clean
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar

cleanall-java:
	- @$(MAKE) -C javaService cleanall
	- @$(MAKE) -C sqlParser cleanall
	- @$(MAKE) -C sqlppParser cleanall
	- @$(MAKE) -C jrulesParser cleanall
	- @rm -rf bin/services
	- @rm -f bin/javaService.jar


## Runtime
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

cleanall-runtimes:
	- @$(MAKE) -C runtimes/javascript cleanall
	- @$(MAKE) -C runtimes/java cleanall
	- @$(MAKE) -C runtimes/spark2 cleanall


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

## Runners
qcert-runners:
ifneq ($(JAVA),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Building the query runners"
	@echo "[Q*cert] "
	@$(MAKE) -C javaRunners all install
else
	@echo "[Q*cert] "
	@echo "[Q*cert] JAVA is not enabled: Not building the query runners"
	@echo "[Q*cert] "
endif

clean-runners:
	- @$(MAKE) -C javaRunners clean
	- @rm -rf bin/lib
	- @rm -f bin/javaRunners.jar

cleanall-runners:
	- @$(MAKE) -C javaRunners cleanall
	- @rm -rf bin/lib
	- @rm -f bin/javaRunners.jar

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
	@$(MAKE) -C coq documentation


## Cleanup
clean: Makefile.coq remove_all_derived
	- @$(MAKE) clean-coq
	- @$(MAKE) clean-ocaml
	- @$(MAKE) clean-java
	- @$(MAKE) clean-runtimes
	- @$(MAKE) clean-demo
	- @$(MAKE) clean-runners
	- @$(MAKE) clean-tests
	- @rm -f Makefile.coq
	- @rm -f *~

cleanall: Makefile.coq remove_all_derived
	- @$(MAKE) cleanall-coq
	- @$(MAKE) cleanall-ocaml
	- @$(MAKE) cleanall-java
	- @$(MAKE) cleanall-runtimes
	- @$(MAKE) cleanall-demo
	- @$(MAKE) cleanall-runners
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

