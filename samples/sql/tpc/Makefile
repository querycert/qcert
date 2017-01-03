SAMPLES=../..
QCERT=$(SAMPLES)/..
SQLPARSER=$(QCERT)/sqlParser
JAVASCRIPT=$(QCERT)/runtime/javascript
QCERTCOMP=$(QCERT)/bin/qcert
# Default assume Java 8 in path
JAVA=java

# Set up Java classpath
ifeq ($(OS),Windows_NT)
    PATH_SEP := ';'
else
    PATH_SEP := ':'
endif
EMPTY=
BLANK=$(EMPTY) $(EMPTY)
RAWCPATH=$(SQLPARSER)/bin $(SAMPLES)/bin $(wildcard $(SQLPARSER)/lib/*.jar)
CPATH=$(subst $(BLANK),$(PATH_SEP),$(RAWCPATH))

# Define merged Javascript runtime
MERGED_RT = $(JAVASCRIPT)/qcert-merged-runtime.js
BASE_RT = $(JAVASCRIPT)/qcert-runtime.js
DATES_RT = $(JAVASCRIPT)/sqlDates.js

# Define lists for TPC-H, the subset of TPC-H that runs in reasonable time, and TPC-DS (compile only)
# Parse failures are omitted from the TPC-DS list.  These are currently 2, 27, 36, 70, and 86.
FAST_TPCH_QUERIES = q1 q3 q4 q6 q10 q11 q12 q14 q15 q16 q17 q18 q19 q20 q21 q22
SLOW_TPCH_QUERIES = q2 q5 q7 q8 q9
RUN_LIST = $(foreach N,$(FAST_TPCH_QUERIES),run_$(N))
SQLTPCDSNUM = 1 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 28 29 30 31 32 33 34 35 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 87 88 89 90 91 92 93 94 95 96 97 98 99
TPCDS_QUERIES = $(foreach N,$(SQLTPCDSNUM),tpcds_$(N))
ALL_QUERIES = $(FAST_TPCH_QUERIES) $(SLOW_TPCH_QUERIES) $(TPCDS_QUERIES)
COMPILE_LIST = $(foreach N,$(ALL_QUERIES),$(N).js)

# By default, we compile all the TPC-H queries and all but 5 TPC-DS queries (those don't even parse).  We the subset of TPC-H queries that run in reasonable time
all:	prereq $(COMPILE_LIST) $(RUN_LIST)

# The prereq target simply ensures that other required builds are done
prereq:
	$(MAKE) -C $(SQLPARSER) classes
	$(MAKE) -C $(SAMPLES) classes

# Target to produce merged runtime
$(MERGED_RT): $(BASE_RT) $(DATES_RT)
	@echo "Creating full SQL JavaScript runtime"
	cat $(BASE_RT) $(DATES_RT) > $(MERGED_RT)

# Compile a query to Javascript and also produce a stats report (as QUERYNAME_stats.json)
%.js:	%.sql
	@echo Compiling $<
	-$(QCERTCOMP) -stat-tree -source sql -target js $<

# Run a Javascript result against the standard dataset (only valid for TPC-H and not all queries complete in reasonable time)
run_%:	%.js tpch.data $(MERGED_RT)
	@echo Running $<
	-time $(JAVA) -cp $(CPATH) testing.runners.RunJavascript -input tpch.data -runtime $(MERGED_RT) $<

# Produce the TPC-H dataset from tables and schema
tpch.data:	dss.ddl customer.tbl lineitem.tbl nation.tbl orders.tbl part.tbl partsupp.tbl region.tbl supplier.tbl
	$(JAVA) -cp $(CPATH) org.qcert.sql.TableTransformer -schema dss.ddl -output tpch.data customer lineitem nation orders part partsupp region supplier

clean:
	-rm *.js *_stats.json tpch.data

