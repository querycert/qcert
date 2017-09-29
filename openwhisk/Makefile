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

all: deploy

init:
	npm install

../runtimes/javascript/quoted-qcert-runtime.js:
	$(MAKE) -C ../runtimes/javascript

src/cloudant-link-runtime.ts: src/cloudant-link-runtime.tmpl ../runtimes/javascript/quoted-qcert-runtime.js
	(cat ../runtimes/javascript/quoted-qcert-runtime.js; \
         cat src/cloudant-link-runtime.tmpl \
         ) > src/cloudant-link-runtime.ts

compile: src/cloudant-link-runtime.ts
	./node_modules/.bin/tsc


deploy: compile
	$(MAKE) -C ../javaService whisk_deploy
	./tools/cli/deploy

undeploy:
	- ./tools/cli/undeploy
	$(MAKE) -C ../javaService whisk_undeploy

tests:

clean:
	rm -rf _build

cleanall: undeploy clean
	rm -rf *~

realcleanall: cleanall
	rm -rf node_modules package-lock.json

.PHONY: init compile deploy undeploy tests clean cleanall realcleanall
