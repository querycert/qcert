# Sigmod 2017 benchmark

This directory reproduce the figures of the paper _Handling
Environments in a Nested Relational Algebra with Combinators and an
Implementation in a Verified Query Compiler_ published at Sigmod 2017.


It supposes that `qcert` is compiled and that the TPC-H queries name
`q*.sql` are present in the directory. Then, to produce the figures,
you have to type:
```
make
```

It generates the pdf files corresponding to the figures in the paper:
- Figure 7 (a): `test_tpch.json_size.pdf`
- Figure 7 (b): `test_tpch.json_depth.pdf`
- Figure 7 (c): `test_tpch.json_timing.pdf`
- Figure 8 (a): `test_all.json_camp_size.pdf`
- Figure 8 (b): `test_all.json_camp_depth.pdf`
- Figure 8 (c): `test_all.json_camp_timing.pdf`
- Figure 9 (a): `test_all.json_nra_size.pdf`
- Figure 9 (b): `test_all.json_nra_depth.pdf`
- Figure 9 (c): `test_all.json_nnrc_size.pdf`


## CAMP Tests

JRules with Customer/Purchase model.

p01.  `example from Figure 5 of ECOOP 2015 paper`
p02.  `c:Customer(age == 32)`
p03.  `c:Customer(); p:Purchase(cid == c.cid);`
p04.  `c:Customer(); not p:Purchase(cid == c.cid);`
p05.  `c1:Customer(); c2:Customer(age == c1.age); not evaluate (c1 == c2);`
p06.  `cs: aggregate { c:Entity(); } do { count {c}; }`
p07.  `the number of Customers, where the age of each Customer equals 32`
p08.  `the minimum age of all Customers`
p09.  `ps: aggregate { c:Customer(name == "John Doe"); p:Purchase(cid == c.cid ); } do { count {p.name}; }`
p10.  `c:Customer(); cs: aggregate { c2:Customer( age == c.age ); } do { count {c2}; }`
p11.  `c:Customer(); cs: aggregate { c2:Customer( age == c.age ); } do { count {c2}; } not evaluate (cs == 1);`
p12.  `c:Customer(); pu: aggregate { p:Purchase(cid == c.cid); } do { ArrayList<String> { p.name }; }`
p13.  `total:aggregate { c:Customer(); pu: aggregate { p:Purchase(cid == c.cid); } do { ArrayList<String> { p.name }; } } do { count { pu }; }`
p14.  `s:aggregate { c:Customer(age <= 34); pu: aggregate { p:Purchase(cid == c.cid); } do { count { p }; } } do { sum { pu }; }`
      n:`aggregate { c:Customer(age <= 34); pu: aggregate { p:Purchase(cid == c.cid); } do { count { p }; } } do { count { pu }; }`
