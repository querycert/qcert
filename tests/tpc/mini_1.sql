select
	count(*) as count
from
	lineitem
where
	l_shipdate <= date '1993-12-01';
