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

CPATH=$(subst $(BLANK),$(PATH_SEP),../runtimes/java/bin ../bin/javaRunners.jar ../bin/lib/*)
JAVAC=javac

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


## OQL
OQLPERSONSNUM=1 2 3 4 5 6 7 8
OQLWORLDNUM=1 2
OQLTARGETS=oql nraenv nnrc nnrcmr cldmr nra nraenv_core nnrc_core dnnrc # dnnrc_typed

oql-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] OQL tests"
	@echo "[Q*cert] "
	@$(MAKE) oql-world-tests
	@$(MAKE) oql-persons-tests

oql-world-tests: 
	@$(foreach N,$(OQLWORLDNUM), \
            $(foreach T,$(OQLTARGETS), \
	       $(QCERTCOMP) -source oql -target $(T) oql/world$(N).oql \
                            -eval -input oql/world.input \
                            -schema oql/world.schema \
                            -eval-validate -output oql/world$(N).out;))

oql-persons-tests:
	@$(foreach N,$(OQLPERSONSNUM), \
            $(foreach T,$(OQLTARGETS), \
	       $(QCERTCOMP) -source oql -target $(T) oql/persons$(N).oql \
                            -eval -input oql/persons.input \
                            -schema oql/persons.schema \
                            -eval-validate -output oql/persons$(N).out;))

## λ-NRA
LAMBDANRAPERSONSNUM=1 2 3 4 5 6 7
LAMBDANRATARGETS=lambda_nra nraenv nnrc nnrcmr cldmr nra nraenv_core nnrc_core dnnrc # dnnrc_typed

lambda_nra-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] λ-NRA tests"
	@echo "[Q*cert] "
	@$(MAKE) lambda_nra-persons-tests

lambda_nra-persons-tests:
	@$(foreach N,$(LAMBDANRAPERSONSNUM), \
            $(foreach T,$(LAMBDANRATARGETS), \
	       $(QCERTCOMP) -source lambda_nra -target $(T) lambda_nra/persons$(N).lnra \
                            -eval -input lambda_nra/persons.input \
                            -schema lambda_nra/persons.schema \
                            -eval-validate -output lambda_nra/persons$(N).out;))

## CAMP
CAMPWORLDNUM=1
CAMPTARGETS=camp nraenv nnrc nnrcmr cldmr nra nraenv_core nnrc_core dnnrc # dnnrc_typed

camp-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] CAMP tests"
	@echo "[Q*cert] "
	@$(MAKE) camp-world-tests

camp-world-tests:
	@$(foreach N,$(CAMPWORLDNUM), \
            $(foreach T,$(CAMPTARGETS), \
	       $(QCERTCOMP) -source camp -target $(T) camp/world$(N).camp \
                            -eval -input camp/world.input \
                            -schema camp/world.schema \
                            -eval-validate -output camp/world$(N).out;))

## SQL
SQLORGNUM=1 2 3 4 5
SQLTARGETS=nraenv nnrc nnrcmr cldmr nra nraenv_core nnrc_core dnnrc # dnnrc_typed

sql-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] SQL tests"
	@echo "[Q*cert] "
	@$(MAKE) sql-org-tests

sql-org-tests:
	@$(foreach N,$(SQLORGNUM), \
            $(foreach T,$(SQLTARGETS), \
	       $(QCERTCOMP) -source sql -target $(T) sql/org$(N).sql \
                            -eval -input sql/org.input \
                            -schema sql/org.schema \
                            -eval-validate -output sql/org$(N).out;))

## TECHRULE
TECHRULETESTNUM=01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 22 #20
TECHRULETARGETS=camp_rule camp nraenv nnrc nnrcmr cldmr nra nraenv_core nnrc_core dnnrc # dnnrc_typed

tech_rule-tests:
	@echo "[Q*cert] "
	@echo "[Q*cert] ODM Rules tests"
	@echo "[Q*cert] "
	@$(MAKE) tech_rule-test-tests

tech_rule-test-tests:
	@$(foreach N,$(TECHRULETESTNUM), \
            $(foreach T,$(TECHRULETARGETS), \
	       $(QCERTCOMP) -source tech_rule -target $(T) tech_rule/test$(N).arl \
                            -eval -input tech_rule/test.input \
                            -schema tech_rule/test.schema \
                            -eval-validate -output tech_rule/test$(N).out;))

