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
DEPENDENCIES=lib/asterix-lang-sqlpp-0.9.1.jar \
	     lib/asterix-lang-common-0.9.1.jar \
	     lib/asterix-common-0.9.1.jar \
	     lib/algebricks-common-0.3.1.jar\
	     lib/hyracks-dataflow-common-0.3.1.jar\
	     lib/algebricks-core-0.3.1.jar \
	     lib/hyracks-api-0.3.1.jar \
	     lib/log4j-1.2.17.jar \
	     lib/asterix-runtime-0.9.1.jar \
	     lib/asterix-om-0.9.1.jar
CPATH=$(subst $(BLANK),$(PATH_SEP),../javaService/bin ../javaService/lib/gson-2.7.jar $(DEPENDENCIES))

JAVAC=javac

LANG=sqlpp

TESTS=tests/1.sqlpp tests/2.sqlpp tests/4.sqlpp tests/5.sqlpp tests/addOperator.sqlpp tests/ANYInFieldAccessor.sqlpp \
	tests/columnalias.sqlpp tests/columnalias2.sqlpp tests/columnalias3.sqlpp tests/constant.sqlpp tests/fieldAccessor.sqlpp \
	tests/from_collection_array.sqlpp tests/from_collection_bag.sqlpp tests/from_inner_correlate.sqlpp tests/from_inner_flatten.sqlpp \
	tests/from_inner_join.sqlpp tests/from_left_correlate2.sqlpp tests/from_where_select_clause.sqlpp \
	tests/groupby_clause_count.sqlpp tests/IfInFLOWGR.sqlpp tests/IfThenElse.sqlpp tests/LetFor.sqlpp \
	tests/ListConstructor.sqlpp tests/mulOperator.sqlpp tests/nestedFLWOGR.sqlpp tests/nestedFLWOGR1.sqlpp tests/nestedFLWOGR2.sqlpp \
	tests/nestedFLWOGR3.sqlpp tests/nestedFor.sqlpp tests/numberInFieldAccessor.sqlpp tests/select_clause_sugar.sqlpp \
	tests/select_from_where_sugar.sqlpp tests/tuple_nav.sqlpp tests/tuple_nav_delimited_identifier.sqlpp tests/tuple_nav_mutiple_steps.sqlpp \
	tests/tuple_nav_quotes.sqlpp tests/variables.sqlpp tests/where_clause.sqlpp \
	tests/q1.sqlpp tests/q2.sqlpp tests/q3.sqlpp tests/q4.sqlpp tests/q5.sqlpp tests/q6.sqlpp tests/q7.sqlpp tests/q8.sqlpp \
	tests/q9.sqlpp tests/q10.sqlpp tests/q11.sqlpp tests/q12.sqlpp tests/q13.sqlpp tests/q14.sqlpp tests/q15.sqlpp tests/q16.sqlpp \
	tests/q17.sqlpp tests/q18.sqlpp tests/q19.sqlpp tests/q20.sqlpp tests/q21.sqlpp tests/q22.sqlpp \
	tests/org1.sql tests/org2.sql tests/org3.sql tests/org4.sql tests/org5.sql \
	tests/tpch_1.sql tests/tpch_2.sql tests/tpch_3.sql tests/tpch_4.sql tests/tpch_5.sql tests/tpch_6.sql tests/tpch_7.sql \
	tests/tpch_8.sql tests/tpch_9.sql tests/tpch_10.sql tests/tpch_11.sql tests/tpch_12.sql tests/tpch_13.sql tests/tpch_14.sql \
	tests/tpch_15.sql tests/tpch_16.sql tests/tpch_17.sql tests/tpch_18.sql tests/tpch_19.sql tests/tpch_20.sql tests/tpch_21.sql tests/tpch_22.sql

# These do not work at present and probably won't in the near future
UNUSED_TESTS=tests/6.sqlpp tests/from_left_correlate.sqlpp tests/from_left_outer_join.sqlpp tests/functionDecl1.sqlpp tests/functionDecl3.sqlpp \
	tests/union.sqlpp tests/utf-8.sqlpp tests/functionDecl.sqlpp tests/functionDecl2.sqlpp     

J_SEXP=$(patsubst %.sqlpp,%_j.sexp,$(TESTS))

JS=$(patsubst %.sqlpp,%.js,$(patsubst %.sql,%.js,$(TESTS)))

O_SEXP=$(patsubst %.sqlpp,%_sqlpp.sexp,$(TESTS))

all:
	$(MAKE) -C ../javaService all
	$(MAKE) classes
	ant -f export.xml

classes: $(CLASSES)

# Right now, we are not testing .js generation routinely.  This tests the s-expression round trips for SQL++ through the Coq AST
unit_tests:	$(O_SEXP)

tests/%_j.sexp:	tests/%.sqlpp
	java -cp bin$(PATH_SEP)$(CPATH) org.qcert.sqlpp.SqlppEncoder $<

tests/%.js:	tests/%.sqlpp
	-../bin/qcert -source $(LANG) $<

tests/%.js:	tests/%.sql
	-../bin/qcert -source $(LANG) $<

tests/%_sqlpp.sexp:	tests/%.sqlpp tests/%_j.sexp
	-../bin/qcert -source sqlpp -target sqlpp -emit-sexp $<
	-java -cp bin$(PATH_SEP)$(CPATH) org.qcert.util.SExpParser tests/$*_j.sexp $@

$(CLASSES): $(JAVA_SRCS) $(DEPENDENCIES)
	-mkdir -p bin
	$(JAVABASE)javac -g -sourcepath src -d bin -cp $(CPATH) $(JAVA_SRCS)

$(DEPENDENCIES):
	ant -f getDependencies.xml

clean:
	@rm -rf bin/*

cleanall: clean
	@rm -f $(DEPENDENCIES)

cleantests:
	-@rm tests/*.js tests/*.txt tests/*.sexp

.PRECIOUS:	$(J_SEXP)
