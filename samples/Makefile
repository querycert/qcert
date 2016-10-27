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

#SQLEXPERIMENT has to be set to run SQL queries
SQLEXPERIMENT=
SQLTABLES=$(SQLEXPERIMENT)/small-tables/tpch_json.io
SQLQUERIES=q2 q11 q16 q17 q19 q22 q101 q103 q104 q106
# Parse failures omitted from the following.  These are currently 2, 27, 36, 70, and 86.
# Split statement support activated for 14, 23, 24, and 39 (each has two statements)
SQLTPCDSNUM = 1 3 4 5 6 7 8 9 10 11 12 13 14_0 14_1 15 16 17 18 19 20 21 22 23_0 23_1 24_0 24_1 25 26 28 29 30 31 32 33 34 35 37 38 39_0 39_1 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 87 88 89 90 91 92 93 94 95 96 97 98 99
SQLTPCDS=$(foreach N,$(SQLTPCDSNUM),sql_tpcds_$(N))

../runtime/javascript/qcert-merged-runtime.js: ../runtime/javascript/qcert-runtime.js ../runtime/javascript/sqlDates.js
	@echo "Creating full SQL JavaScript runtime"
	cat ../runtime/javascript/qcert-runtime.js ../runtime/javascript/sqlDates.js > ../runtime/javascript/qcert-merged-runtime.js

tpcds:	$(SQLTPCDS)

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

sqlstat_%:
	@echo "Parsing SQL: " $(subst sqlstat_,,$@)
	$(MAKE) -C $(SQLEXPERIMENT) $(subst sqlstat_,sql_,$@)
	@cp $(SQLEXPERIMENT)/sexp/$(subst sqlstat_,,$@).s-sql sql
	@echo "Generating SQL Stats:" $(subst sqlstat_,,$@)
	$(QCERTCOMP) -stat-tree -source sql -target js sql/$(subst sqlstat_,,$@).s-sql

clean:
	@rm -rf bin/*
	@rm -f oql/*.js
	@rm -f oql/*.java
	@rm -f oql/*.class

