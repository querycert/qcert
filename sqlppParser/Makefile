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
ifeq ($(OS),Windows_NT)
  PATH_SEP=';'
else
  PATH_SEP=':'
endif

JAVA_SRCS=$(wildcard src/org/qcert/sqlpp/*.java)
CLASSES=$(patsubst %.java,%.class,$(patsubst src/%,bin/%,$(JAVA_SRCS)))

EMPTY=
BLANK=$(EMPTY) $(EMPTY)

# Keep this list accurate as dependencies evolve or versions change
DEPENDENCIES=lib/algebricks-common-0.3.1.jar lib/algebricks-core-0.3.1.jar lib/asterix-common-0.9.1.jar lib/asterix-lang-common-0.9.1.jar \
	lib/asterix-lang-sqlpp-0.9.1.jar lib/asterix-om-0.9.1.jar lib/asterix-runtime-0.9.1.jar lib/hyracks-api-0.3.1.jar \
	lib/hyracks-dataflow-common-0.3.1.jar lib/log4j-1.2.17.jar

CPATH=$(subst $(BLANK),$(PATH_SEP),../javaService/bin ../javaService/lib/gson-2.7.jar $(DEPENDENCIES))

JAVAC=javac

TESTS=tests/1.sqlpp tests/2.sqlpp tests/4.sqlpp tests/5.sqlpp tests/6.sqlpp tests/addOperator.sqlpp tests/ANYInFieldAccessor.sqlpp \
	tests/columnalias.sqlpp tests/columnalias2.sqlpp tests/columnalias3.sqlpp tests/constant.sqlpp tests/fieldAccessor.sqlpp \
	tests/from_collection_array.sqlpp tests/from_collection_bag.sqlpp tests/from_inner_correlate.sqlpp tests/from_inner_flatten.sqlpp \
	tests/from_inner_join.sqlpp tests/from_left_correlate.sqlpp tests/from_left_correlate2.sqlpp tests/from_left_outer_join.sqlpp \
	tests/from_where_select_clause.sqlpp tests/functionDecl.sqlpp tests/functionDecl1.sqlpp tests/functionDecl2.sqlpp \
	tests/functionDecl3.sqlpp tests/groupby_clause_count.sqlpp tests/IfInFLOWGR.sqlpp tests/IfThenElse.sqlpp tests/LetFor.sqlpp \
	tests/ListConstructor.sqlpp tests/mulOperator.sqlpp tests/nestedFLWOGR.sqlpp tests/nestedFLWOGR1.sqlpp tests/nestedFLWOGR2.sqlpp \
	tests/nestedFLWOGR3.sqlpp tests/nestedFor.sqlpp tests/numberInFieldAccessor.sqlpp tests/select_clause_sugar.sqlpp \
	tests/select_from_where_sugar.sqlpp tests/tuple_nav.sqlpp tests/tuple_nav_delimited_identifier.sqlpp tests/tuple_nav_mutiple_steps.sqlpp \
	tests/tuple_nav_quotes.sqlpp tests/union.sqlpp tests/utf-8.sqlpp tests/variables.sqlpp tests/where_clause.sqlpp

S_EXPRESSIONS=$(patsubst %.sqlpp,%.p.s-sql,$(TESTS))

JS=$(patsubst %.sqlpp,%.js,$(TESTS))

all:
	$(MAKE) classes
	ant -f export.xml

classes: $(CLASSES)

echoes:
	echo $(TESTS)
	echo $(S_EXPRESSIONS)
	echo $(JS)

unit_tests:	$(JS)

$(S_EXPRESSIONS):	$(TESTS)
	java -cp bin$(PATH_SEP)$(CPATH) org.qcert.sqlpp.SqlppEncoder $(TESTS)

tests/%.js:	tests/%.p.s-sql
	-../bin/qcert -source sql -source-sexp $<

$(CLASSES): $(JAVA_SRCS) $(DEPENDENCIES)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

$(DEPENDENCIES):
	ant -f getDependencies.xml

clean:
	@rm -rf bin/*
