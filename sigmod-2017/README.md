CAMP Tests
----------

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
