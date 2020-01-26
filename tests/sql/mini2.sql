select
	l_returnflag,
  count(*) as count
from
	lineitem
where
	l_shipdate <= date '1993-12-01'
group by
	l_returnflag;