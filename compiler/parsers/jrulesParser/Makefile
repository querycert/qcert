# 
#  Copyright (C) 2017 Joshua Auerbach 
# 
#  Licensed under the Apache License, Version 2.0 (the "License");
#  you may not use this file except in compliance with the License.
#  You may obtain a copy of the License at
# 
#  http://www.apache.org/licenses/LICENSE-2.0
# 
#  Unless required by applicable law or agreed to in writing, software
#  distributed under the License is distributed on an "AS IS" BASIS,
#  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#  See the License for the specific language governing permissions and
#  limitations under the License.
# 

# Might need to set these if Java is not in the path
JAVA=java
JAVAC=javac

# The following MUST be set on the cmdline or in the environment if the 'designer' target is used (otherwise ignore)
#WORKSPACE = location of folder that is the parent of all designer projects (usually the ODM Designer workspace)

# Remaining entries can be left as is

QCERTCOMP=../../../bin/qcert
RAWCPATH=bin ../javaService/bin ../javaService/lib/gson-2.7.jar ../javaService/lib/commons-csv-1.1.jar $(wildcard lib/*.jar)

JAVA_SRCS=$(shell find src/ -name '*.java')
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))
# Keep dependencies up to date
OSS_DEPENDENCIES=lib/asm-3.1.jar lib/asm-commons-3.1.jar lib/asm-tree-3.1.jar
DEPENDENCIES = $(OSS_DEPENDENCIES) lib/jrules-engine.jar 

ifeq ($(OS),Windows_NT)
  PATH_SEP=';'
else
  PATH_SEP=':'
endif

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

CPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWCPATH))

ENTITIES_TYPES = Customer Purchase MainEntity
BRANDING_TYPES = Client Marketer ProductRep Product
ALL_TYPES = $(foreach T,$(ENTITIES_TYPES),tests.entities.$(T)) $(foreach T,$(BRANDING_TYPES),tests.branding.$(T))
DATAFILES = $(foreach F,$(ALL_TYPES),data/$(F).csv)
DESIGNER_RULES = MiniLoanService::eligibility.'minimum credit score' MiniLoanService::eligibility.'minimum income' MiniLoanService::validation.'maximum amount'

all:
	$(MAKE) -C ../javaService all
	$(MAKE) classes
	ant -f export.xml

all_js:	$(JSTESTS)

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS) $(DEPENDENCIES)
	-mkdir -p bin
	$(JAVAC) -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

$(OSS_DEPENDENCIES):
	ant -f getDependencies.xml

designer:
	$(JAVA) -cp $(CPATH) org.qcert.camp.translator.Rule2CAMP -workspace $(WORKSPACE) -output data $(DESIGNER_RULES)

data/testInput:	data/testSchema.json $(DATAFILES)
	$(JAVA) -cp $(CPATH) org.qcert.util.DataLoader -dir data -output testInput -schema testSchema.json $(ALL_TYPES)

clean:
	-rm -rf bin/*
	-rm -f data/*.js
	-rm -f data/*.camp
	-rm -f data/*_output.json
	-rm -f data/*_test.json

cleanall: clean
	@rm -f $(OSS_DEPENDENCIES) # Be careful not to delete jrules-engine.jar

