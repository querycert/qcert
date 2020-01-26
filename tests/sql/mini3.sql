select
	distinct( l_returnflag )
from
	lineitem
where
	l_shipdate <= date '1993-12-01';