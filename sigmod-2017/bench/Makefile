QCERT=../bin/qcert

ALL_CAMP=p01.camp \
	p02.camp \
	p03.camp \
	p04.camp \
	p05.camp \
	p06.camp \
	p07.camp \
	p08.camp \
	p09.camp \
	p10.camp \
	p11.camp \
	p12.camp \
	p13.camp \
	p14.camp

TPCH=q1.sql \
	q2.sql \
	q3.sql \
	q4.sql \
	q5.sql \
	q6.sql \
	q7.sql \
	q8.sql \
	q9.sql \
	q10.sql \
	q11.sql \
	q12.sql \
	q14.sql \
	q15.sql \
	q16.sql \
	q17.sql \
	q18.sql \
	q19.sql \
	q20.sql \
	q21.sql \
	q22.sql

ALL_STATS=$(patsubst %.camp,%_stats.json,$(ALL_CAMP))
TPCH_STATS=$(patsubst %.sql,%_stats.json,$(TPCH))

all: pdf

pdf: test_tpch.json test_all.json
	./tools/print-sql.py test_tpch.json
	./tools/print-camp.py test_all.json


test_all.json: tools/jsonpp $(ALL_STATS)
	./tools/jsonpp $(ALL_STATS) > $@

test_tpch.json: tools/jsonpp $(TPCH_STATS)
	./tools/jsonpp $(TPCH_STATS) > $@

%_stats.json: %.camp
	$(QCERT) -stat-tree $<

%_stats.json: %.sql
	$(QCERT) -source sql -stat-tree $<

tools/jsonpp:
	$(MAKE) -C tools jsonpp

clean:
	rm -f $(ALL_STATS) $(TPCH_STATS) \
		$(patsubst %.camp,%.js,$(ALL_CAMP)) \
		$(patsubst %.sql,%.js,$(TPCH))

cleanall: clean
	rm -f *~ \
		test_all.json test_all.json_*.pdf \
		test_tpch.json test_tpch.json_*.pdf

.PHONY: %_stats.json
