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

include ../Makefile.config

ifeq ($(OS),Windows_NT)
  PATH_SEP=';'
else
  PATH_SEP=':'
endif

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

CPATH=$(subst $(BLANK),$(PATH_SEP),../runtimes/java/bin ../bin/javaRunner.jar ../bin/lib/*)
NPMPATH=../clis/nodejs/bin
JAVAC=javac
JAVARUN=java
NODERUN=node

#
QCERTCOMP=../bin/qcert
QCERTEVAL=../bin/qcert -eval

# Default target just builds the code
all:
	@$(MAKE) tests

tests:
	@$(MAKE) oql-tests
	@$(MAKE) lambda_nra-tests
	@$(MAKE) camp-tests
ifneq ($(SQL),)
	@$(MAKE) sql-tests
endif
ifneq ($(JRULES),)
	@$(MAKE) tech_rule-tests
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
	sql-org-tests sql-org-tests-js sql-org-tests-java \
	tech_rule-tests \
	tech_rule-test-tests tech_rule-test-tests-js tech_rule-test-tests-java \
	designer_rule-tests \
	designer_rule-test-tests \
	clean

## OQL
OQLPERSONSNUM=1 2 3 4 5 6 7 8 9 10 11 12
OQLWORLDNUM=1 2
OQLSTRINGNUM=1 2 3
OQLEMPLOYEESNUM=1 2
OQLTARGETS=oql nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_qcert # dnnrc_typed

oql-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] OQL tests"
	@echo "[Q*cert] "
	@$(MAKE) oql-string-tests
	@$(MAKE) oql-world-tests
	@$(MAKE) oql-persons-tests
	@$(MAKE) oql-employees-tests
ifneq ($(JAVASCRIPT),)
	@$(MAKE) oql-string-tests-js
	@$(MAKE) oql-world-tests-js
	@$(MAKE) oql-persons-tests-js
	@$(MAKE) oql-employees-tests-js
endif
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
	       $(NODERUN) $(NPMPATH)/qcertRun.js compile \
                          --source oql \
                          --input oql/string.input \
                          --schema oql/string.schema \
                          --output oql/string$(N).out \
                          --eval-validate \
                          --query oql/string$(N).oql || exit 1 ;)
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
	       $(NODERUN) $(NPMPATH)/qcertRun.js compile \
                          --source oql \
                          --input oql/world.input \
                          --schema oql/world.schema \
                          --output oql/world$(N).out \
                          --eval-validate \
                          --query oql/world$(N).oql || exit 1 ;)
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
	       $(NODERUN) $(NPMPATH)/qcertRun.js compile \
                          --source oql \
                          --input oql/persons.input \
                          --schema oql/persons.schema \
                          --output oql/persons$(N).out \
                          --eval-validate \
                          --query oql/persons$(N).oql || exit 1 ;)

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
	       $(NODERUN) $(NPMPATH)/qcertRun.js compile \
                          --source oql \
                          --input oql/employees.input \
                          --schema oql/employees.schema \
                          --output oql/employees$(N).out \
                          --eval-validate \
                          --query oql/employees$(N).oql || exit 1 ;)
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

## λ-NRA
LAMBDANRAPERSONSNUM=0 1 2 3 4 5 6 7
LAMBDANRATARGETS=lambda_nra nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_qcert # dnnrc_typed

lambda_nra-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] λ-NRA tests"
	@echo "[Q*cert] "
	@$(MAKE) lambda_nra-persons-tests
ifneq ($(JAVASCRIPT),)
	@$(MAKE) lambda_nra-persons-tests-js
endif
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
	@$(foreach N,$(LAMBDANRAPERSONSNUM), \
	       $(NODERUN) $(NPMPATH)/qcertRun.js compile \
                          --source lambda_nra \
                          --input lambda_nra/persons.input \
                          --schema lambda_nra/persons.schema \
                          --output lambda_nra/persons$(N).out \
                          --eval-validate \
                          --query lambda_nra/persons$(N).lnra || exit 1 ;)
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
CAMPTARGETS=camp nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_qcert # dnnrc_typed

camp-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] CAMP tests"
	@echo "[Q*cert] "
	@$(MAKE) camp-world-tests
ifneq ($(JAVASCRIPT),)
	@$(MAKE) camp-world-tests-js
endif
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
	       $(NODERUN) $(NPMPATH)/qcertRun.js compile \
                          --source camp \
                          --input camp/world.input \
                          --schema camp/world.schema \
                          --output camp/world$(N).out \
                          --eval-validate \
                          --query camp/world$(N).camp || exit 1 ;)
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
SQLORGNUM=1 2 3 4 5 6 7 8 9 10 11
SQLTARGETS=nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_qcert # dnnrc_typed

sql-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL tests"
	@echo "[Q*cert] "
	@$(MAKE) sql-org-tests
ifneq ($(JAVASCRIPT),)
	@$(MAKE) sql-org-tests-js
endif
ifneq ($(JAVA),)
	@$(MAKE) sql-org-tests-java
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
	       $(QCERTCOMP) -source sql  -target js sql/org$(N).sql \
                            -eval-validate -schema sql/org.schema; \
	       $(NODERUN) $(NPMPATH)/qcertRun.js execute \
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


## TECHRULE
TECHRULETESTNUM=01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 22 #20
TECHRULETARGETS=camp_rule camp nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_qcert # dnnrc_typed

tech_rule-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM Tech Rules tests"
	@echo "[Q*cert] "
	@$(MAKE) tech_rule-test-tests
ifneq ($(JAVASCRIPT),)
	@$(MAKE) tech_rule-test-tests-js
endif
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
                            -eval-validate -schema tech_rule/test.schema; \
	       $(JAVARUN) -cp $(CPATH) testing.runners.RunJavascript \
                          -runtime ../runtimes/javascript/qcert-runtime.js \
                          -input tech_rule/test.input \
                          -schema tech_rule/test.schema \
                          -output tech_rule/test$(N).out \
                          tech_rule/test$(N).js || exit 1;)
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
DESIGNERRULETARGETS=camp_rule camp nraenv nnrc nnrs nnrs_imp nnrcmr nra nraenv_core nnrc_core dnnrc imp_qcert # dnnrc_typed

designer_rule-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM Designer Rules tests"
	@echo "[Q*cert] "
	@$(MAKE) designer_rule-test-tests
ifneq ($(JAVASCRIPT),)
	@$(MAKE) designer_rule-test-tests-js
endif

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
                            -eval-validate -schema designer_rule/test.schema; \
	       $(JAVARUN) -cp $(CPATH) testing.runners.RunJavascript \
                          -runtime ../runtimes/javascript/qcert-runtime.js \
                          -input designer_rule/test.input \
                          -schema designer_rule/test.schema \
                          -output designer_rule/test$(N).out \
                          designer_rule/test$(N).js || exit 1;)

clean:
	@rm -f */*.txt
	@rm -f oql/*.json
	@rm -f oql/*.js
	@rm -f oql/*.java
	@rm -f oql/*.class
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

cleanall: clean
	@rm -f *~ */*~
