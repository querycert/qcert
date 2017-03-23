TPC_H=tpch_2_17_0/dbgen
TPCH_QGEN=$(TPC_H)/qgen
TPC_DS=v2.3.0

TPCH_NUMBERS=1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22
TPCDS_NUMBERS=1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99

TPCH_TEMPLATES=$(foreach,N,$(TPCH_NUMBERS),$(TPC_H)/queries/$(N).sql)
TPCH_SQL=$(foreach,N,$(TPCH_NUMBERS),../tpch_$(N).sql)

# Must run on LINUX.  The following sets up to detect that while making minimal assumptions.
ifeq ($(OS),Windows_NT)
		SYSTEM_TEST=$(error "No support for building TPC tools on windows: must use a Linux system")
else
ifeq (Linux,$(shell uname -s))
		SYSTEM_TEST=-echo Running on a Linux system.  Proceeding with TPC tools build.
else
		SYSTEM_TEST=$(error "Must build TPC tools on a Linux system")
endif
endif

all:	test_system gen_h gen_ds

test_system:
	$(SYSTEM_TEST)

gen_h:	$(TPCH_QGEN) $(TPCH_SQL)

../tpch_%.sql:	$(TPC_H)/queries/%.sql
	(cd $(TPC_H)/queries && ../qgen -d -c -b ../dists.dss -s 1 $*) > $@

$(TPCH_QGEN):	$(TPC_H)
	sed -e 's/^CC .*/CC=gcc/' -e 's/^DATABASE.*/DATABASE=DB2/' -e 's/^MACHINE.*/MACHINE=LINUX/' -e 's/^WORKLOAD.*/WORKLOAD=TPCH/' $(TPC_H)/makefile.suite > $(TPC_H)/Makefile
	$(MAKE) -C $(TPC_H)

$(TPC_H):
	unzip tpc-h-tool.zip $(TPC_H)/*

gen_ds:
	#TODO
