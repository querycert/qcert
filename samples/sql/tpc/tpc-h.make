# This makefile drives the generation of SQL source for TPC-H

all:	test_system tpch_2_17_0/dbgen/qgen

tpch_2_17_0/dbgen/makefile.suite:
	unzip $(TPC_H_ZIP) tpch_2_17_0/dbgen/*

tpch_2_17_0/dbgen/makefile:	tpch_2_17_0/dbgen/makefile.suite
	sed -e 's/^CC .*/CC=gcc/' -e 's/^DATABASE.*/DATABASE=DB2/' -e 's/^MACHINE.*/MACHINE=LINUX/' -e 's/^WORKLOAD.*/WORKLOAD=TPCH/' $< > $@

tpch_2_17_0/dbgen/qgen:	tpch_2_17_0/dbgen/makefile
	$(MAKE) -C tpch_2_17_0/dbgen

# Must run on LINUX.  The following attempts to detect that while making minimal assumptions.
test_system:
ifeq ($(OS),Windows_NT)
		$(error "No support for building TPC tools on windows: must use a Linux system")
else ifneq(Linux,$(shell uname -s))
		$(error "Must build TPC tools on a Linux system")
else
		echo Running on a Linux system.  Proceeding with TPC tools build.
endif
