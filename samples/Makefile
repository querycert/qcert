JAVA_SRCS=$(wildcard src/testing/runners/*.java)
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))

ifeq ($(OS),Windows_NT)
  PATH_SEP=';'
else
  PATH_SEP=':'
endif

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

RAWCPATH=bin ../runtime/java/bin $(wildcard ../lib/*.jar)
CPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWCPATH))

JAVA=java
JAVAC=javac
QCERTCOMP=../bin/qcert
QCERTEVAL=../bin/qcert -eval

all:
	$(MAKE) classes

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

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

