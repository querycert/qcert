TPC_H=tpch_2_17_0/dbgen
TPCH_QGEN=$(TPC_H)/qgen

TPCH_NUMBERS=1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21 22

TPCH_SQL=$(foreach N,$(TPCH_NUMBERS),../q$(N).sql)

# Must run on LINUX.  The following sets up to detect that while making minimal assumptions.
ifeq ($(OS),Windows_NT)
		SYSTEM_TEST=$(error "No support for building TPC tools on windows: must use a Linux system")
else
ifeq (Linux,$(shell uname -s))
		SYSTEM_TEST=@echo Running on a Linux system.  Proceeding with TPC tools build.
else
		SYSTEM_TEST=$(error "Must build TPC tools on a Linux system")
endif
endif

all:	test_system $(TPCH_SQL) ../dss.ddl zip

zip:
	cd .. && zip tpc.zip *.sql *.ddl

test_system:
	$(SYSTEM_TEST)

../q%.sql: $(TPCH_QGEN)
	(cd $(TPC_H)/queries && ../qgen -d -c -b ../dists.dss -s 1 $*) > $@

$(TPCH_QGEN):	$(TPC_H)
	sed -e 's/^CC .*/CC=gcc/' -e 's/^DATABASE.*/DATABASE=DB2/' -e 's/^MACHINE.*/MACHINE=LINUX/' -e 's/^WORKLOAD.*/WORKLOAD=TPCH/' $(TPC_H)/makefile.suite > $(TPC_H)/Makefile
	$(MAKE) -C $(TPC_H)

$(TPC_H):
	unzip *tpc-h-tool.zip $(TPC_H)/*

../dss.ddl:	$(TPC_H)/dss.ddl
	cp $< $@

clean:
	-rm	../dss.ddl
	-rm -fr $(TPC_H)
	-rm ../*.sql
