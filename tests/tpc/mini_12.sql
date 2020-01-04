select
	l_shipdate
from
	lineitem
where
	l_shipdate > date '1993-12-01';
