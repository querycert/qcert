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

include ../Makefile.config

ifeq ($(OS),Windows_NT)
  PATH_SEP=';'
else
  PATH_SEP=':'
endif

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

CPATH=$(subst $(BLANK),$(PATH_SEP),../runtimes/java/bin ../bin/javaRunner.jar ../bin/lib/*)
NPMPATH=../cli/nodejs/bin
JAVAC=javac
JAVARUN=java
NODERUN=node

#
QCERTCOMP=../_build/default/cli/ocaml/qcert.exe
QCERTEVAL=../_build/default/cli/ocaml/qcert.exe -eval

# Default target just builds the code
all:
	@$(MAKE) tests

tests:
	@$(MAKE) oql-tests
	@$(MAKE) lambda_nra-tests
	@$(MAKE) camp-tests
	@$(MAKE) imp_ejson-tests
ifneq ($(JAVA),)
ifneq ($(SQL),)
	@$(MAKE) sql-tests
endif
ifneq ($(JRULES),)
	@$(MAKE) tech_rule-tests
endif
endif

.PHONY: oql-tests \
	oql-world-tests oql-world-tests-js oql-world-tests-java \
	oql-persons-tests oql-persons-tests-js oql-persons-tests-java \
	oql-employees-tests oql-employees-tests-js oql-employees-tests-java \
	lambda_nra-tests \
	lambda_nra-persons-tests lambda_nra-persons-tests-js lambda_nra-persons-tests-java \
	camp-tests \
	camp-world-tests camp-world-tests-js camp-world-tests-java \
	sql-tests \
	sql-org-tests sql-org-tests-js sql-org-tests-java sql-mini-tests sql-mini-tests-js sql-mini-tests-java \
	tech_rule-tests \
	tech_rule-test-tests tech_rule-test-tests-js tech_rule-test-tests-java \
	designer_rule-tests \
	designer_rule-test-tests \
	imp_ejson-tests \
	clean

## OQL
OQLPERSONSNUM=1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
OQLWORLDNUM=1 2
OQLSTRINGNUM=0 1 2 3
OQLEMPLOYEESNUM=1 2
OQLTARGETS=oql nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_data imp_ejson # dnnrc_typed

oql-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] OQL tests"
	@echo "[Q*cert] "
	@$(MAKE) oql-string-tests
	@$(MAKE) oql-world-tests
	@$(MAKE) oql-persons-tests
	@$(MAKE) oql-employees-tests
	@$(MAKE) oql-string-tests-js
	@$(MAKE) oql-world-tests-js
	@$(MAKE) oql-persons-tests-js
	@$(MAKE) oql-persons-tests-js2
	@$(MAKE) oql-employees-tests-js
	@$(MAKE) oql-tests-wasm
ifneq ($(JAVA),)
	@$(MAKE) oql-string-tests-java
	@$(MAKE) oql-world-tests-java
	@$(MAKE) oql-persons-tests-java
	@$(MAKE) oql-employees-tests-java
endif

oql-string-tests:
	$(foreach N,$(OQLSTRINGNUM), \
            $(foreach T,$(OQLTARGETS), \
	       $(QCERTCOMP) -source oql -target $(T) oql/string$(N).oql \
                            -eval -input oql/string.input \
                            -schema oql/string.schema \
                            -eval-validate -output oql/string$(N).out || exit 1;))
oql-string-tests-js:
	@$(foreach N,$(OQLSTRINGNUM), \
	       $(QCERTCOMP) -source oql -target javascript oql/string$(N).oql -schema oql/string.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input oql/string.input \
                          --schema oql/string.schema \
                          --output oql/string$(N).out \
                          --eval-validate \
                          --query oql/string$(N).js || exit 1 ;)
oql-string-tests-java:
	@$(foreach N,$(OQLSTRINGNUM), \
	       $(QCERTCOMP) -source oql -target java oql/string$(N).oql \
                            -eval-validate -schema oql/string.schema; \
	       $(JAVAC) -cp $(CPATH) oql/string$(N).java; \
	       $(JAVARUN) -cp $(CPATH):oql testing.runners.RunJava \
                          -input oql/string.input \
                          -schema oql/string.schema \
                          -output oql/string$(N).out \
                          string$(N) || exit 1;)
oql-world-tests:
	$(foreach N,$(OQLWORLDNUM), \
            $(foreach T,$(OQLTARGETS), \
	       $(QCERTCOMP) -source oql -target $(T) oql/world$(N).oql \
                            -eval -input oql/world.input \
                            -schema oql/world.schema \
                            -eval-validate -output oql/world$(N).out || exit 1;))
oql-world-tests-js:
	@$(foreach N,$(OQLWORLDNUM), \
	       $(QCERTCOMP) -source oql -target javascript oql/world$(N).oql -schema oql/world.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input oql/world.input \
                          --schema oql/world.schema \
                          --output oql/world$(N).out \
                          --eval-validate \
                          --query oql/world$(N).js || exit 1 ;)
oql-world-tests-java:
	@$(foreach N,$(OQLWORLDNUM), \
	       $(QCERTCOMP) -source oql -target java oql/world$(N).oql \
                            -eval-validate -schema oql/world.schema; \
	       $(JAVAC) -cp $(CPATH) oql/world$(N).java; \
	       $(JAVARUN) -cp $(CPATH):oql testing.runners.RunJava \
                          -input oql/world.input \
                          -schema oql/world.schema \
                          -output oql/world$(N).out \
                          world$(N) || exit 1;)

oql-persons-tests:
	@$(foreach N,$(OQLPERSONSNUM), \
            $(foreach T,$(OQLTARGETS), \
	       $(QCERTCOMP) -source oql -target $(T) oql/persons$(N).oql \
                            -eval -input oql/persons.input \
                            -schema oql/persons.schema \
                            -eval-validate -output oql/persons$(N).out || exit 1;))
oql-persons-tests-js:
	@$(foreach N,$(OQLPERSONSNUM), \
	       $(QCERTCOMP) -source oql -target javascript oql/persons$(N).oql -schema oql/persons.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input oql/persons.input \
                          --schema oql/persons.schema \
                          --output oql/persons$(N).out \
                          --eval-validate \
                          --query oql/persons$(N).js || exit 1 ;)
oql-persons-tests-js2:
	@$(foreach N,$(OQLPERSONSNUM), \
	       $(QCERTCOMP) -exact-path -source oql -path nraenv -path nraenv -path nnrc -path nnrc -path nnrs -path nnrs_imp -path nnrs_imp -path imp_data -path imp_ejson -path imp_ejson -path js_ast -target javascript oql/persons$(N).oql -schema oql/persons.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input oql/persons.input \
                          --schema oql/persons.schema \
                          --output oql/persons$(N).out \
                          --eval-validate \
                          --query oql/persons$(N).js || exit 1 ;)

oql-persons-tests-java:
	@$(foreach N,$(OQLPERSONSNUM), \
	       $(QCERTCOMP) -source oql -target java oql/persons$(N).oql \
                            -eval-validate -schema oql/persons.schema; \
	       $(JAVAC) -cp $(CPATH) oql/persons$(N).java; \
	       $(JAVARUN) -cp $(CPATH):oql testing.runners.RunJava \
                          -input oql/persons.input \
                          -schema oql/persons.schema \
                          -output oql/persons$(N).out \
                          persons$(N) || exit 1;)

oql-employees-tests:
	@$(foreach N,$(OQLEMPLOYEESNUM), \
            $(foreach T,$(OQLTARGETS), \
	       $(QCERTCOMP) -source oql -target $(T) oql/employees$(N).oql \
                            -eval -input oql/employees.input \
                            -schema oql/employees.schema \
                            -eval-validate -output oql/employees$(N).out || exit 1;))
oql-employees-tests-js:
	@$(foreach N,$(OQLEMPLOYEESNUM), \
	       $(QCERTCOMP) -source oql -target javascript oql/employees$(N).oql -schema oql/employees.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input oql/employees.input \
                          --schema oql/employees.schema \
                          --output oql/employees$(N).out \
                          --eval-validate \
                          --query oql/employees$(N).js || exit 1 ;)
oql-employees-tests-java:
	@$(foreach N,$(OQLEMPLOYEESNUM), \
	       $(QCERTCOMP) -source oql -target java oql/employees$(N).oql \
                            -eval-validate -schema oql/employees.schema; \
	       $(JAVAC) -cp $(CPATH) oql/employees$(N).java; \
	       $(JAVARUN) -cp $(CPATH):oql testing.runners.RunJava \
                          -input oql/employees.input \
                          -schema oql/employees.schema \
                          -output oql/employees$(N).out \
                          employees$(N) || exit 1;)
## OQL
OQLWASMPERSONSNUM=1 2 3 4 5 6 7 8 9 10 11 12 # 13 14
OQLWASMWORLDNUM=1 2
OQLWASMSTRINGNUM=0 1 2 3
OQLWASMEMPLOYEESNUM=1 2

oql-tests-wasm:
	@$(MAKE) oql-string-tests-wasm
	@$(MAKE) oql-world-tests-wasm
	@$(MAKE) oql-persons-tests-wasm
	@$(MAKE) oql-employees-tests-wasm

oql-string-tests-wasm:	# compilation-only test
	@$(foreach N,$(OQLWASMSTRINGNUM), \
	       $(QCERTCOMP) -source oql -target wasm oql/string$(N).oql -schema oql/string.schema -quiet || exit 1; )

oql-world-tests-wasm:	# compilation-only test
	@$(foreach N,$(OQLWASMWORLDNUM), \
	       $(QCERTCOMP) -source oql -target wasm oql/world$(N).oql -schema oql/world.schema -quiet || exit 1;)

oql-persons-tests-wasm:	# compilation-only test
	@$(foreach N,$(OQLWASMPERSONSNUM), \
	       $(QCERTCOMP) -source oql -target wasm oql/persons$(N).oql -schema oql/persons.schema -quiet || exit 1; )

oql-employees-tests-wasm:	# compilation-only test
	@$(foreach N,$(OQLWASMEMPLOYEESNUM), \
	       $(QCERTCOMP) -source oql -target wasm oql/employees$(N).oql -schema oql/employees.schema -quiet || exit 1; )

## λ-NRA
LAMBDANRAPERSONSNUM=0 1 2 3 4 5 6 7 8 9 10 11 12 13 14
LAMBDANRATARGETS=lambda_nra nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_data imp_ejson # dnnrc_typed

lambda_nra-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] λ-NRA tests"
	@echo "[Q*cert] "
	@$(MAKE) lambda_nra-persons-tests
	@$(MAKE) lambda_nra-persons-tests-js
ifneq ($(JAVA),)
	@$(MAKE) lambda_nra-persons-tests-java
endif

lambda_nra-persons-tests:
	@$(foreach N,$(LAMBDANRAPERSONSNUM), \
            $(foreach T,$(LAMBDANRATARGETS), \
	       $(QCERTCOMP) -source lambda_nra -target $(T) lambda_nra/persons$(N).lnra \
                            -eval -input lambda_nra/persons.input \
                            -schema lambda_nra/persons.schema \
                            -eval-validate -output lambda_nra/persons$(N).out || exit 1;))
lambda_nra-persons-tests-js:
	$(foreach N,$(LAMBDANRAPERSONSNUM), \
	       $(QCERTCOMP) -source lambda_nra -target javascript lambda_nra/persons$(N).lnra -schema lambda_nra/persons.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input lambda_nra/persons.input \
                          --schema lambda_nra/persons.schema \
                          --output lambda_nra/persons$(N).out \
                          --eval-validate \
                          --query lambda_nra/persons$(N).js || exit 1 ;)
lambda_nra-persons-tests-java:
	@$(foreach N,$(LAMBDANRAPERSONSNUM), \
	       $(QCERTCOMP) -source lambda_nra -target java lambda_nra/persons$(N).lnra \
                            -eval-validate -schema lambda_nra/persons.schema; \
	       $(JAVAC) -cp $(CPATH) lambda_nra/persons$(N).java; \
	       $(JAVARUN) -cp $(CPATH):lambda_nra testing.runners.RunJava \
                          -input lambda_nra/persons.input \
                          -schema lambda_nra/persons.schema \
                          -output lambda_nra/persons$(N).out \
                          persons$(N) || exit 1;)

## CAMP
CAMPWORLDNUM=1
CAMPTARGETS=camp nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_data imp_ejson # dnnrc_typed

camp-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] CAMP tests"
	@echo "[Q*cert] "
	@$(MAKE) camp-world-tests
	@$(MAKE) camp-world-tests-js
ifneq ($(JAVA),)
	@$(MAKE) camp-world-tests-java
endif

camp-world-tests:
	@$(foreach N,$(CAMPWORLDNUM), \
            $(foreach T,$(CAMPTARGETS), \
	       $(QCERTCOMP) -source camp -target $(T) camp/world$(N).camp \
                            -eval -input camp/world.input \
                            -schema camp/world.schema \
                            -eval-validate -output camp/world$(N).out || exit 1;))
camp-world-tests-js:
	@$(foreach N,$(CAMPWORLDNUM), \
	       $(QCERTCOMP) -source camp -target javascript camp/world$(N).camp -schema camp/world.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input camp/world.input \
                          --schema camp/world.schema \
                          --output camp/world$(N).out \
                          --eval-validate \
                          --query camp/world$(N).js || exit 1 ;)
camp-world-tests-java:
	@$(foreach N,$(CAMPWORLDNUM), \
	       $(QCERTCOMP) -source camp -target java camp/world$(N).camp \
                            -eval-validate -schema camp/world.schema; \
	       $(JAVAC) -cp $(CPATH) camp/world$(N).java; \
	       $(JAVARUN) -cp $(CPATH):camp testing.runners.RunJava \
                          -input camp/world.input \
                          -schema camp/world.schema \
                          -output camp/world$(N).out \
                          world$(N) || exit 1;)

## SQL
SQLORGNUM=1 2 3 4 5 6 7 8 9 10 11 12
SQLMININUM=1 2
SQLTARGETS=nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_data imp_ejson # dnnrc_typed

sql-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL tests"
	@echo "[Q*cert] "
	@$(MAKE) sql-org-tests
	@$(MAKE) sql-mini-tests
	@$(MAKE) sql-org-tests-js
	@$(MAKE) sql-mini-tests-js
ifneq ($(JAVA),)
	@$(MAKE) sql-org-tests-java
	@$(MAKE) sql-mini-tests-java
endif

sql-org-tests:
	@$(foreach N,$(SQLORGNUM), \
            $(foreach T,$(SQLTARGETS), \
	       $(QCERTCOMP) -source sql -target $(T) sql/org$(N).sql \
                            -eval -input sql/org.input \
                            -schema sql/org.schema \
                            -eval-validate -output sql/org$(N).out || exit 1;))
sql-org-tests-js:
	@$(foreach N,$(SQLORGNUM), \
	       $(QCERTCOMP) -source sql -target js sql/org$(N).sql \
                            -eval-validate -schema sql/org.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input sql/org.input \
                          --schema sql/org.schema \
                          --output sql/org$(N).out \
                          --eval-validate \
                          --query sql/org$(N).js || exit 1 ;)
sql-org-tests-java:
	@$(foreach N,$(SQLORGNUM), \
	       $(QCERTCOMP) -source sql -target java sql/org$(N).sql \
                            -eval-validate -schema sql/org.schema; \
	       $(JAVAC) -cp $(CPATH) sql/org$(N).java; \
	       $(JAVARUN) -cp $(CPATH):sql testing.runners.RunJava \
                          -input sql/org.input \
                          -schema sql/org.schema \
                          -output sql/org$(N).out \
                          org$(N) || exit 1;)

sql-mini-tests:
	@$(foreach N,$(SQLMININUM), \
            $(foreach T,$(SQLTARGETS), \
	       $(QCERTCOMP) -source sql -target $(T) sql/mini$(N).sql \
                            -eval -input sql/mini.input \
                            -schema sql/mini.schema \
                            -eval-validate -output sql/mini$(N).out || exit 1;))
sql-mini-tests-js:
	@$(foreach N,$(SQLMININUM), \
	       $(QCERTCOMP) -source sql -target js sql/mini$(N).sql \
                            -eval-validate -schema sql/mini.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input sql/mini.input \
                          --schema sql/mini.schema \
                          --output sql/mini$(N).out \
                          --eval-validate \
                          --query sql/mini$(N).js || exit 1 ;)
sql-mini-tests-java:
	@$(foreach N,$(SQLMININUM), \
	       $(QCERTCOMP) -source sql -target java sql/mini$(N).sql \
                            -eval-validate -schema sql/mini.schema; \
	       $(JAVAC) -cp $(CPATH) sql/mini$(N).java; \
	       $(JAVARUN) -cp $(CPATH):sql testing.runners.RunJava \
                          -input sql/mini.input \
                          -schema sql/mini.schema \
                          -output sql/mini$(N).out \
                          mini$(N) || exit 1;)

## TECHRULE
TECHRULETESTNUM=01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 22 #20
TECHRULETARGETS=camp_rule camp nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_data imp_ejson # dnnrc_typed

tech_rule-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM Tech Rules tests"
	@echo "[Q*cert] "
	@$(MAKE) tech_rule-test-tests
	@$(MAKE) tech_rule-test-tests-js
ifneq ($(JAVA),)
	@$(MAKE) tech_rule-test-tests-java
endif

tech_rule-test-tests:
	@$(foreach N,$(TECHRULETESTNUM), \
            $(foreach T,$(TECHRULETARGETS), \
	       $(QCERTCOMP) -source tech_rule -target $(T) tech_rule/test$(N).arl \
                            -eval -input tech_rule/test.input \
                            -schema tech_rule/test.schema \
                            -eval-validate -output tech_rule/test$(N).out || exit 1;))
tech_rule-test-tests-js:
	@$(foreach N,$(TECHRULETESTNUM), \
	       $(QCERTCOMP) -source tech_rule  -target js tech_rule/test$(N).arl \
                            -eval-validate -schema tech_rule/test.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input tech_rule/test.input \
                          --schema tech_rule/test.schema \
                          --output tech_rule/test$(N).out \
                          --eval-validate \
                          --query tech_rule/test$(N).js || exit 1 ;)
tech_rule-test-tests-java:
	@$(foreach N,$(TECHRULETESTNUM), \
	       $(QCERTCOMP) -source tech_rule -target java tech_rule/test$(N).arl \
                            -eval-validate -schema tech_rule/test.schema; \
	       $(JAVAC) -cp $(CPATH) tech_rule/test$(N).java; \
	       $(JAVARUN) -cp $(CPATH):tech_rule testing.runners.RunJava \
                          -input tech_rule/test.input \
                          -schema tech_rule/test.schema \
                          -output tech_rule/test$(N).out \
                          test$(N) || exit 1;)

## DESIGNERRULE
DESIGNERRULETESTNUM=
DESIGNERRULETARGETS=camp_rule camp nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_data imp_ejson # dnnrc_typed

designer_rule-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM Designer Rules tests"
	@echo "[Q*cert] "
	@$(MAKE) designer_rule-test-tests
	@$(MAKE) designer_rule-test-tests-js

designer_rule-test-tests:
	@$(foreach N,$(DESIGNERRULETESTNUM), \
            $(foreach T,$(DESIGNERRULETARGETS), \
	       $(QCERTCOMP) -source designer_rule -target $(T) designer_rule/test$(N).agg \
                            -eval -input designer_rule/test.input \
                            -schema designer_rule/test.schema \
                            -eval-validate -output designer_rule/test$(N).out || exit 1;))
designer_rule-test-tests-js:
	@$(foreach N,$(DESIGNERRULETESTNUM), \
	       $(QCERTCOMP) -source designer_rule -target js designer_rule/test$(N).agg \
                            -eval-validate -schema designer_rule/test.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input designer_rule/test.input \
                          --schema designer_rule/test.schema \
                          --output designer_rule/test$(N).out \
                          --eval-validate \
                          --query designer_rule/test$(N).js || exit 1 ;)

## IMPEJSON
IMPEJSONTARGETS=imp_ejson wasm_ast # dnnrc_typed
IMPEJSONWASMNUM=0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 16 17 18 19 20 21
# TODO 15 seems to be an error representation issue

imp_ejson-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] Imp (EJSON) tests"
	@echo "[Q*cert] "
	@$(MAKE) imp_ejson-wasm-spec-tests
	@$(MAKE) imp_ejson-js-tests
	@$(MAKE) imp_ejson-wasm-node-tests

# imp_ejson -> wasm ; run on spec interpreter
imp_ejson-wasm-spec-tests:
	$(foreach N,$(IMPEJSONWASMNUM), \
            $(foreach T,$(IMPEJSONTARGETS), \
	       $(QCERTCOMP) -source imp_ejson -target $(T) imp_ejson/wasm$(N).imp_ejson \
                            -eval -input imp_ejson/wasm.input \
                            -schema imp_ejson/wasm.schema \
                            -eval-validate -output imp_ejson/wasm$(N).out || exit 1;))

IMPEJSONWASMALTNUM=0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18
# TODO. Why does this run 15?
imp_ejson-wasm-spec-alt-tests:
	$(foreach N,$(IMPEJSONWASMALTNUM), \
				 $(QCERTCOMP) imp_ejson/wasm$(N).imp_ejson \
				 		-source imp_ejson -path imp_ejson -target imp_ejson \
						-quiet \
						-schema imp_ejson/wasm.schema \
						-eval -input imp_ejson/wasm.input && \
		     $(QCERTCOMP) imp_ejson/wasm$(N).imp_ejson \
				 		-source imp_ejson -target wasm_ast \
				 		-eval -eval-validate \
				 		-schema imp_ejson/wasm.schema \
		     		-input imp_ejson/wasm.input \
				 		-output imp_ejson/wasm$(N)_imp_ejson.json || exit 1; )

IMPEJSONJSNUM=0 1 2 3 4 5 6 7 8 9 10 11 12 14 16 17 18
# 13 is failure in javascript (different block scoping between Imp and JS)
# TODO 15 throws exception

# imp_ejson -> javascript ; run on node
imp_ejson-js-tests:
	$(foreach N,$(IMPEJSONJSNUM), \
	       $(QCERTCOMP) -source imp_ejson -target javascript imp_ejson/wasm$(N).imp_ejson -schema imp_ejson/wasm.schema -quiet; \
	       $(NODERUN) $(NPMPATH)/qcert.js execute \
                          --input imp_ejson/wasm.input \
                          --schema imp_ejson/wasm.schema \
                          --output imp_ejson/wasm$(N).out \
                          --eval-validate \
                          --query imp_ejson/wasm$(N).js || exit 1; )

IMPEJSONWASMNODENUM=0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21

# imp_ejson -> wasm ; run on node
imp_ejson-wasm-node-tests:
	$(foreach N,$(IMPEJSONWASMNODENUM), \
				 $(QCERTCOMP) imp_ejson/wasm$(N).imp_ejson \
				 		-source imp_ejson -path imp_ejson -target imp_ejson \
						-quiet \
						-schema imp_ejson/wasm.schema \
						-eval -input imp_ejson/wasm.input && \
	       $(QCERTCOMP) imp_ejson/wasm$(N).imp_ejson \
						-quiet \
						-source imp_ejson -target wasm \
						-schema imp_ejson/wasm.schema && \
				 $(NODERUN) ../runtimes/assemblyscript/cli-runner.js \
				 		../runtimes/assemblyscript/build/optimized.wasm \
						imp_ejson/wasm$(N).wasm \
						imp_ejson/wasm.input \
						imp_ejson/wasm$(N)_imp_ejson.json || exit 1; )

clean:
	@rm -rf log
	@rm -f */*.txt
	@rm -f oql/*.json
	@rm -f oql/*.js
	@rm -f oql/*.java
	@rm -f oql/*.class
	@rm -f oql/*.wat
	@rm -f oql/*.wasm
	@rm -f sql/*.json
	@rm -f sql/*.js
	@rm -f sql/*.java
	@rm -f sql/*.class
	@rm -f tech_rule/*.json
	@rm -f tech_rule/*.js
	@rm -f tech_rule/*.java
	@rm -f tech_rule/*.class
	@rm -f tech_rule/*_camp.camp
	@rm -f tech_rule/*_rule.camp
	@rm -f designer_rule/*.json
	@rm -f designer_rule/*.js
	@rm -f designer_rule/*.java
	@rm -f designer_rule/*.class
	@rm -f designer_rule/*_camp.camp
	@rm -f designer_rule/*_rule.camp
	@rm -f camp/*.json
	@rm -f camp/*.js
	@rm -f camp/*.java
	@rm -f camp/*.class
	@rm -f camp/*_camp.camp
	@rm -f lambda_nra/*.json
	@rm -f lambda_nra/*.js
	@rm -f lambda_nra/*.java
	@rm -f lambda_nra/*.class
	@rm -f imp_ejson/*.json
	@rm -f imp_ejson/*.js
	@rm -f imp_ejson/*.java
	@rm -f imp_ejson/*.class
	@rm -f imp_ejson/*.wat
	@rm -f imp_ejson/*.wasm

cleanall: clean
	@rm -f *~ */*~
