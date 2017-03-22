# This makefile drives the generation of SQL source for TPC-H

# Must run on LINUX.  The following attempts to detect that while making minimal assumptions.
ifeq ($(OS),Windows_NT)
		SYSTEM_TEST=$(error "No support for building TPC tools on windows: must use a Linux system")
else
ifeq (Linux,$(shell uname -s))
		SYSTEM_TEST=echo Running on a Linux system.  Proceeding with TPC tools build.
else
		SYSTEM_TEST=$(error "Must build TPC tools on a Linux system")
endif
endif

all:	test_system tpch_2_17_0/dbgen/qgen

test_system:
	$(SYSTEM_TEST)

tpch_2_17_0/dbgen/makefile.suite:
	unzip $(TPC_H_ZIP) tpch_2_17_0/dbgen/*

tpch_2_17_0/dbgen/makefile:	tpch_2_17_0/dbgen/makefile.suite
	sed -e 's/^CC .*/CC=gcc/' -e 's/^DATABASE.*/DATABASE=DB2/' -e 's/^MACHINE.*/MACHINE=LINUX/' -e 's/^WORKLOAD.*/WORKLOAD=TPCH/' $< > $@

tpch_2_17_0/dbgen/qgen:	tpch_2_17_0/dbgen/makefile
	$(MAKE) -C tpch_2_17_0/dbgen
