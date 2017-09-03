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
ifeq ($(OS),Windows_NT)
  PATH_SEP=';'
else
  PATH_SEP=':'
endif

JAVA_SRCS=$(wildcard src/testing/runners/*.java)
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

# Keep this list accurate as dependencies evolve or versions change
DEPENDENCIES=lib/cloudant-client-1.2.3-sources.jar \
	     lib/cloudant-client-1.2.3.jar \
	     lib/commons-codec-1.9-sources.jar \
	     lib/commons-codec-1.9.jar \
	     lib/commons-collections-3.2.2-sources.jar \
	     lib/commons-collections-3.2.2.jar \
	     lib/commons-logging-1.2-sources.jar \
	     lib/commons-logging-1.2.jar \
	     lib/gson-2.7-sources.jar \
	     lib/gson-2.7.jar \
	     lib/httpclient-4.5.2-sources.jar \
	     lib/httpclient-4.5.2.jar \
	     lib/httpcore-4.4.5-sources.jar \
	     lib/httpcore-4.4.5.jar \
	     lib/junit-4.9-sources.jar \
	     lib/junit-4.9.jar
CPATH=$(subst $(BLANK),$(PATH_SEP),../runtime/java/bin $(DEPENDENCIES))

JAVAC=javac

# Default target just builds the code
all:
	$(MAKE) classes

# Install target
install:
	ant -f export.xml

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS) $(DEPENDENCIES)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

$(DEPENDENCIES):
	ant -f getDependencies.xml

# Compilation targets
QCERTCOMP=../bin/qcert
QCERTEVAL=../bin/qcert -eval

oql/%.js: oql/%.oql
	@echo
	@echo "Compiling test with Q*cert: '"$<"' to '"$@"'"
	$(QCERTCOMP) -source oql -target js $<

oql/%.java: oql/%.oql
	@echo
	@echo "Compiling test with Q*cert: '"$<"' to '"$@"'"
	$(QCERTCOMP) -source oql -target java $<

oql/%.class: oql/%.java
	@echo
	@echo "Compiling test with javac: '"$<"' to '"$@"'"
	$(JAVAC) -cp $(CPATH) $<

# Run targets
JAVA=java

run_js_%: oql/%.js
	@echo
	@echo "Running test: '"$<"' on data: oql/persons.input"
	@echo
	$(JAVA) -cp bin:$(CPATH) testing.runners.RunJavascript -input oql/persons.input -runtime ../runtime/javascript/qcert-runtime.js $< 

run_java_%: oql/%.class
	@echo
	@echo "Running test: '"$<"' on data: oql/persons.input"
	@echo
	$(JAVA) -cp bin:$(CPATH):oql testing.runners.RunJava -input oql/persons.input $*

clean:
	@rm -rf bin/*
	@rm -f oql/*.js
	@rm -f oql/*.java
	@rm -f oql/*.class

cleanall: clean
	@rm -f $(DEPENDENCIES)

# There's no 21, and 20 uses the not-yet-implemented groupBy.
TESTNUMBERS = 00 01 02 03 04 05 06 07 08 09 10 11 12 13 14 15 16 17 18 19 22
# Note that test 06 executes and produce a result we believe to be correct.  For some reason, ODM produces what we think is an incorrect result.
# All other tests in TESTNUMBERS produce results identical to ODM.
CAMPTESTS = $(foreach N,$(TESTNUMBERS),data/test$(N).camp)
JSTESTS =  $(foreach N,$(TESTNUMBERS),data/test$(N).js)
RUNTESTS = $(foreach N,$(TESTNUMBERS),run_test$(N))
