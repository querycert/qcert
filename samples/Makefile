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
QCERTCOMP=../bin/qcert
QCERTEVAL=../bin/qcert -eval
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
	$(QCERTCOMP) -source oql -target js $<

oql/%.java: oql/%.oql
	@echo
	@echo "Compiling test with Q*cert: '"$<"' to '"$@"'"
	$(QCERTCOMP) -source oql -target java $<

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

SQLEXPERIMENT=/Users/js/git/summerCAMP/sql-experiment
SQLTABLES=$(SQLEXPERIMENT)/small-tables/tpch_json.io

../runtime/javascript/qcert-merged-runtime.js: ../runtime/javascript/qcert-runtime.js ../runtime/javascript/sqlDates.js
	@echo "Creating full SQL JavaScript runtime"
	cat ../runtime/javascript/qcert-runtime.js ../runtime/javascript/sqlDates.js > ../runtime/javascript/qcert-merged-runtime.js

sql_%: ../runtime/javascript/qcert-merged-runtime.js
	@echo "Parsing SQL: " $(subst sql_,,$@)
	$(MAKE) -C $(SQLEXPERIMENT) $@
	@cp $(SQLEXPERIMENT)/sexp/$(subst sql_,,$@).s-sql sql
	@echo "Compiling SQL:" $(subst sql_,,$@)
	$(QCERTCOMP) -source sql -target js sql/$(subst sql_,,$@).s-sql
	@echo "Running SQL:" $(subst sql_,,$@)
	time $(JAVA) -cp $(CPATH) testing.runners.RunJavascript -input $(SQLTABLES) -runtime ../runtime/javascript/qcert-merged-runtime.js sql/$(subst sql_,,$@).js 

sqlall_%: ../runtime/javascript/qcert-merged-runtime.js
	@echo "Parsing SQL: " $(subst sqlall_,,$@)
	$(MAKE) -C $(SQLEXPERIMENT) $(subst sqlall_,sql_,$@)
	@cp $(SQLEXPERIMENT)/sexp/$(subst sqlall_,,$@).s-sql sql
	@echo "Compiling SQL:" $(subst sqlall_,,$@)
	$(QCERTCOMP) -emit-all -source sql -target js sql/$(subst sqlall_,,$@).s-sql
	$(JAVA) -cp $(CPATH) testing.runners.RunJavascript -input $(SQLTABLES) -runtime ../runtime/javascript/qcert-merged-runtime.js sql/$(subst sqlall_,,$@).js 

clean:
	@rm -rf bin/*
	@rm -f oql/*.js
	@rm -f oql/*.java
	@rm -f oql/*.class

