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

## Toplevel
all: prepare

prepare: lib/static_config.ml lib/js_runtime.ml

## Extraction
../runtimes/javascript/qcert_runtime.ml:
	$(MAKE) -C ../runtimes/javascript

lib/js_runtime.ml: ../runtimes/javascript/qcert_runtime.ml
	cp ../runtimes/javascript/qcert_runtime.ml lib/js_runtime.ml

lib/static_config.ml:
	echo "(* This file is generated *)" > lib/static_config.ml
	echo "let qcert_home = \"$(QCERT_HOME)\"" >> lib/static_config.ml

## Clean

clean:

cleanall: clean
	$(MAKE) -C ../runtimes/javascript cleanall
	rm -rf lib/js_runtime.ml
	rm -rf lib/static_config.ml
	rm -rf *~

.NOTPARALLEL: 

