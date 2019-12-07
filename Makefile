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

## Full run
all: 
	@$(MAKE) qcert
	@$(MAKE) MAKEFLAGS= qcert-ocaml
	@$(MAKE) MAKEFLAGS= qcert-javascript
ifneq ($(JAVA),)
	@$(MAKE) MAKEFLAGS= qcert-parsersJava
endif
	@$(MAKE) MAKEFLAGS= qcert-runtimes
	@$(MAKE) MAKEFLAGS= qcert-clis


## Compiler Core

qcert: Makefile.coq
	@$(MAKE) qcert-coq

qcert-coq: Makefile.coq
	@echo "[Q*cert] "
	@echo "[Q*cert] Compiling Coq source"
	@echo "[Q*cert] "
	@$(MAKE) -f Makefile.coq

clean-coq:
	- @$(MAKE) -f Makefile.coq clean

cleanall-coq: clean-coq


## Extraction

qcert-ocaml:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to OCaml"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler native

qcert-javascript:
	@echo "[Q*cert] "
	@echo "[Q*cert] Extracting compiler to JavaScript"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler js

clean-ocaml:
	- @$(MAKE) -C compiler clean

cleanall-ocaml:
	- @$(MAKE) -C compiler cleanall


## Java Parsers

qcert-parsersJava:
	@echo "[Q*cert] "
	@echo "[Q*cert] Compling Java parsers"
	@echo "[Q*cert] "
ifneq ($(SQL),)
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL parser"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsersJava/sqlParser
endif
ifneq ($(SQLPP),)
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL++ parser"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsersJava/sqlppParser
endif
ifneq ($(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM rules parsers"
	@echo "[Q*cert] "
	@$(MAKE) -C compiler/parsersJava/jrulesParser
endif
ifneq ($(SQL)$(SQLPP)$(JRULES),)
	@echo "[Q*cert] "
	@echo "[Q*cert] Installing parser service"
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
	@echo "[Q*cert] "
	@echo "[Q*cert] Building CLIs"
	@echo "[Q*cert] "
qcert-clis:
ifneq ($(JAVASCRIPT),)
	@$(MAKE) javascript-cli
endif
ifneq ($(JAVA),)
	@$(MAKE) java-cli
endif

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
	- @$(MAKE) -C clis/java clean
	- @rm -f bin/javaRunner.jar

cleanall-clis:
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


## Install

install-coq:
	@$(MAKE) -f Makefile.coq install


## Documentation
docs:
	@$(MAKE) -C compiler/src documentation

## Cleanup
clean: Makefile.coq remove_all_derived
	- @$(MAKE) clean-coq
	- @$(MAKE) clean-ocaml
	- @$(MAKE) clean-parsersJava
	- @$(MAKE) clean-runtimes
	- @$(MAKE) clean-clis
	- @$(MAKE) clean-demo
	- @$(MAKE) clean-test
	- @rm -f Makefile.coq
	- @rm -f *~

cleanmost: Makefile.coq
	- @$(MAKE) cleanall-ocaml
	- @$(MAKE) cleanall-runtimes
	- @$(MAKE) cleanall-clis
	- @$(MAKE) cleanall-parsersJava
	- @$(MAKE) cleanall-demo
	- @$(MAKE) cleanall-test
	- @rm -f Makefile.coq
	- @rm -f *~

cleanall: Makefile.coq remove_all_derived
	- @$(MAKE) cleanall-coq
	- @$(MAKE) cleanmost

## Misc

clean_detritus:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 ./scripts/remove_detritus_derived_file.sh

remove_all_derived:
	@find . \( -name '*.vo' -or -name '*.v.d' -or -name '*.glob'  -or -name '*.aux' \) -print0 | xargs -0 rm -f

Makefile.coq: Makefile Makefile.coq_modules $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

.PHONY: all clean clean_detritus documentation documentation_old npm qcert

