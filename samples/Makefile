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

RAWCPATH=bin
CPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWCPATH))

RAWRUNCPATH=bin ../runtime/java/bin $(wildcard ../lib/*.jar)
RUNCPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWRUNCPATH))

JAVA=java
JAVAC=javac
QCERTCOMP=../bin/CACo
QCERTEVAL=../bin/CAEv

all:
	$(MAKE) classes

classes: $(CLASSES)

$(CLASSES): $(JAVA_SRCS)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

oql/%.js: oql/%.oql
	@echo
	@echo "Compiling test: '"$<"' to '"$@"'"
	$(QCERTCOMP) -source OQL -target JS $<

oql/%.java: oql/%.oql
	@echo
	@echo "Compiling test: '"$<"' to '"$@"'"
	$(QCERTCOMP) -source OQL -target Java $<

oql/%.class: oql/%.java
	@echo
	@echo "Compiling test: '"$<"' to '"$@"'"
	$(JAVAC) -cp $(RUNCPATH) $<

run_js_%: oql/%.js
	@echo
	@echo "Running test: '"$<"' on data: data/persons.json"
	@echo
	$(JAVA) -cp $(RUNCPATH) testing.runners.RunJavascript -io data/persons.json -runtime ../runtime/javascript/qcert-runtime.js $< 

clean:
	@rm -rf bin/*
	@rm -f oql/*.js
	@rm -f oql/*.java

