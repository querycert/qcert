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

SQL=q1.sql \
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

TPCDS=d01.sql \
	d08.sql \
	d09.sql \
	d10.sql \
	d13.sql \
	d15.sql \
	d19.sql \
	d21.sql \
	d25.sql \
	d26.sql \
	d28.sql \
	d30.sql \
	d32.sql \
	d37.sql \
	d38.sql \
	d41.sql \
	d43.sql \
	d45.sql \
	d48.sql \
	d50.sql \
	d55.sql \
	d56.sql \
	d58.sql \
	d59.sql \
	d60.sql \
	d65.sql \
	d66.sql \
	d69.sql \
	d71.sql \
	d76.sql \
	d81.sql \
	d82.sql \
	d87.sql \
	d88.sql

ALL_STATS=$(patsubst %.camp,%_stats.json,$(ALL_CAMP))
SQL_STATS=$(patsubst %.sql,%_stats.json,$(SQL))
TPCDS_STATS=$(patsubst %.sql,%_stats.json,$(TPCDS))

all: test_all.json test_sql.json

pdf: test_sql.json test_all.json
	./tools/print-sql.py test_sql.json
	./tools/print-stats.py test_all.json
	./tools/print-camp.py test_all.json


test_all.json: $(ALL_STATS)
	./tools/jsonpp $? > $@

test_sql.json: $(SQL_STATS)
	./tools/jsonpp $? > $@

%_stats.json: %.camp
	$(QCERT) -stat-tree $<

%_stats.json: %.sql
	$(QCERT) -source sql -stat-tree $<

clean:
	rm -f $(ALL_STATS) $(SQL_STATS) \
		$(patsubst %.camp,%.js,$(ALL_CAMP)) \
		$(patsubst %.sql,%.js,$(SQL)) \
		$(patsubst %.sql,%.js,$(TPCDS))

cleanall: clean
	rm -f *~

.PHONY: %_stats.json
