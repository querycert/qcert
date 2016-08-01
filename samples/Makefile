export JAVA_TOOL_OPTIONS=-Dfile.encoding=UTF-8
OSTYPE=$(shell uname -o)

JAVA_SRCS=$(wildcard src/testing/runners/*.java)
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))

ifeq ($(OSTYPE),Cygwin)
  PATH_SEP=';'
else
  ifeq ($(OSTYPE),Msys)
    PATH_SEP=';'
  else
    PATH_SEP=':'
  endif
endif

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

RAWCPATH=bin ../runtime/java/bin $(wildcard ../lib/*.jar)
CPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWCPATH))

JAVA=java
JAVAC=javac
QCERTCOMP=../bin/CACo
QCERTEVAL=../bin/CAEv
QCERTDATA=../bin/CADa

all:
	$(MAKE) classes

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

oql/%.js: oql/%.oql
	@echo
	@echo "Compiling test with Q*cert: '"$<"' to '"$@"'"
	$(QCERTCOMP) -source OQL -target JS $<

oql/%.java: oql/%.oql
	@echo
	@echo "Compiling test with Q*cert: '"$<"' to '"$@"'"
	$(QCERTCOMP) -source OQL -target Java $<

oql/%.class: oql/%.java
	@echo
	@echo "Compiling test with javac: '"$<"' to '"$@"'"
	$(JAVAC) -cp $(CPATH) $<

oql/%_spark2:
	-mkdir -p $@
	-mkdir -p $@/src/main/scala

oql/%_spark2/persons.sjson: oql/%_spark2
	$(QCERTDATA) -dir oql/$*_spark2 data/persons.json

camp/%_spark2:
	-mkdir -p $@
	-mkdir -p $@/src/main/scala

run_spark2_%: oql/%_spark2 oql/%_spark2/persons.sjson
	$(QCERTCOMP)

run_js_%: oql/%.js
	@echo
	@echo "Running test: '"$<"' on data: data/persons.json"
	@echo
	$(JAVA) -cp $(CPATH) testing.runners.RunJavascript -input data/persons.json -runtime ../runtime/javascript/qcert-runtime.js $< 

run_java_%: oql/%.class
	@echo
	@echo "Running test: '"$<"' on data: data/persons.json"
	@echo
	$(JAVA) -cp $(CPATH):oql testing.runners.RunJava -input data/persons.json $*

clean:
	@rm -rf bin/*
	@rm -f oql/*.js
	@rm -f oql/*.java
	@rm -f oql/*.class

