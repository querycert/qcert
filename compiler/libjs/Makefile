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
include ../../Makefile.config
# Contains the list of all the Coq modules
include ../../Makefile.coq_modules

## Configuraton
QCERT_HOME=$(CURDIR)/../..

## Mains
MAIN=qcertJS

BYTECODE=bc
JS=js

## Toplevel
all: ../../bin/$(MAIN).js

## JavaScript
../../bin/$(MAIN).js:
	dune build $(MAIN).$(BYTECODE)
	js_of_ocaml $(QCERT_HOME)/_build/default/compiler/libjs/$(MAIN).$(BYTECODE)
	cp $(QCERT_HOME)/_build/default/compiler/libjs/$(MAIN).$(JS) ../../bin/$(MAIN).$(JS)

## Clean

clean:
	rm -f ../../bin/$(MAIN).js

cleanall: clean
	rm -rf *~

.NOTPARALLEL: 

