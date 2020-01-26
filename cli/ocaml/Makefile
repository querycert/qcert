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
MAIN=qcert
MAIN2=qdata

NATIVE=exe
BYTECODE=bc

## Toplevel
all: $(QCERT_HOME)/_build/default/cli/ocaml/$(MAIN).$(NATIVE) $(QCERT_HOME)/_build/default/cli/ocaml/$(MAIN2).$(NATIVE)

$(QCERT_HOME)/_build/default/cli/ocaml/$(MAIN).$(NATIVE):
	dune build $(MAIN).$(NATIVE)

$(QCERT_HOME)/_build/default/cli/ocaml/$(MAIN2).$(NATIVE):
	dune build $(MAIN2).$(NATIVE)

## Install

install: ../../bin/$(MAIN) ../../bin/$(MAIN2)

../../bin/$(MAIN):
	cp $(QCERT_HOME)/_build/default/cli/ocaml/$(MAIN).$(NATIVE) ../../bin/$(MAIN)

../../bin/$(MAIN2):
	cp $(QCERT_HOME)/_build/default/cli/ocaml/$(MAIN2).$(NATIVE) ../../bin/$(MAIN2)

## Clean

clean:
	rm -f ../../bin/$(MAIN)
	rm -f ../../bin/$(MAIN2)

cleanall: clean
	rm -f *~
	rm -f .merlin

.NOTPARALLEL: 

