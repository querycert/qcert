# Q*cert

Overview
========

This is the source code for the QCert certified query compiler. The
primary focus is on building a state of the art query compiler for
languages over a rich data model (nested, hierarchical, etc), and an
implementation which provides correctness guarantees.

Current source languages include:

     - CAMP, the Calculus of Aggregating Matching Patterns [SSH15]
       used to capture the pattern matching and data processing
       semantics of rules languages, such as jRules [BM11]

     - mini-OQL [SS16], a usable query language for objects, which is
       a subset of OQL [ODMG30].

Current targets include:

     - Javascript [JS06], Java [Java7], Cloudant (CouchDB), and Spark
       [Zah12].

The compiler relies a number of intermediate languages for
optimization and code-generation, notably:

A nested-relational algebra:

     - A Nested Relational Algebra (NRA). There are many such
       algebras. We opt for the version from [Clu93,Moe09], which is
       the most developed for optimization purposes. It includes the
       relational algebra as a subset and has been applied
       successfully to a variety of query languages, notably OQL and
       XQuery.

A nested-relational calculus:

     - A Nested Relational Calculus (NNRC). There are many such
       similar calculus. We opt for the named version from [Bus07],
       which makes the encoding of NRA operators natural, and is
       closely related to the 'XQuery core' used in [FSW01].

The compiler includes translations from source to target and an
optimizer which leverages the database algebra and calculus. Those
translations, as well as the optimization rules are proved correct
using the Coq proof assistant.


References
==========

[BM11] Jérôme Boyer, and Hafedh Mili. Agile business rule
development. Springer Berlin Heidelberg, 2011.

[Bus07] Jan van den Bussche, and Stijn Vansummeren. "Polymorphic type
inference for the named nested relational calculus." ACM Transactions
on Computational Logic (TOCL) 9.1 (2007): 3.

[Clu93] Sophie Cluet, and Guido Moerkotte. "Nested Queries in Object
Bases". Proceedings of the Fourth International Workshop on Database
Programming Languages (DBPL'93). pp 226-242.

[Doo95] Robert B. Doorenbos. Production matching for large learning
systems. Dissertation, University of Southern California, 1995.

[FSW01] Mary Fernandez, Jérôme Siméon, and Philip Wadler. "A
Semi-monad for Semi-structured Data." International Conference on
Database Theory (ICDT'2001). Springer Berlin Heidelberg,
2001. 263-300.

[Java7] The Java® Language Specification. James Gosling, Bill Joy, Guy
Steele, Gilad Bracha, Alex Buckley. February 2013. Oracle Corp.

[JS06] David Flanagan. JavaScript: the definitive guide. " O'Reilly
Media, Inc.", 2006.

[Moe09] Guido Moerkotte. Building Query Compilers. Draft
Manuscript. http://pi3.informatik.uni-mannheim.de/~moer/querycompiler.pdf

[ODMG30] Jeff Eastman, et al. The object data standard: ODMG
3.0. Eds. Roderic Geoffrey Galton Cattell, and Douglas
K. Barry. Vol. 1. San Francisco: Morgan Kaufmann, 2000.

[SSH15] Avraham Shinnar, Jérôme Siméon, and Martin Hirzel. "A Pattern
Calculus for Rule Languages: Expressiveness, Compilation, and
Mechanization." 29th European Conference on Object-Oriented
Programming. 2015.

[SS16] Avraham Shinnar and Jérôme Siméon. "Nominal Typing for Data
Languages". Technical Report, IBM. May 2016

[Zah12] Matei Zaharia, et al. "Fast and interactive analytics over
Hadoop data with Spark." USENIX; login 37.4 (2012): 45-51.



Code
====

Prerequisites
-------------

To compiler QCert from the source, you will need:

 - Coq 8.5pl1 (https://coq.inria.fr/)
 - OCaml. It should work with OCaml 4.01 or later
 - The Menhir parser generator. It has been tested with version 20151112
   http://gallium.inria.fr/~fpottier/menhir/

Compilation
-----------

1. Compile the Coq source:

	make
	(or to run make faster: make -j 8)

2. Extract the compiler and built the OCaml frontend:

    cd ./ocaml
	make

This should produce a few executables: CACo for the QCert compiler,
CAEv for the QCert interpreter, and CADa for the QCert data processor.


Testing
-------

see ./queryTests/README

We have a Jenkins based continuous build setup at 
http://camp-test.sl.cloud9.ibm.com:8080/


Organization
------------

./qcert contains the Coq source code
./qcert/ocaml contains the toplevel compiler and code extraction from Coq
./queryTests and ./jrules2coq contains the pre-processor from jRules and testing infrastructure.

./docs/paper contains reference material for the CAMP compiler and conference articles
./docs/external-docs contains related research articles and references documents

Inside the ./qcert directory, the organization is as follows.

Foundational modules:

./coq/Basic/Util contains useful libraries and lemmas, independant of QCert itself
./coq/Basic/Data contains the core data model
./coq/Basic/Operators contains unary/binary operators shared across ILs
./coq/Basic/TypeSystem contains the core type system
./coq/Basic/Typing contains typing and type inference for data and operators

Intermediate languages (ILs), including eval, typing, type inference,
and equivalences/rewrites:

./coq/CAMP contains support for the Calculus of Aggregating Matching Patterns (CAMP)
./coq/NRA contains support for the Nested Relational Algebra (NRA)
./coq/NRAEnv contains support for the extension of NRA with environments
./coq/NNRC contains support for the Named Nested Relational Calculus (NNRC)
./coq/DNNRC contains support for the Distributed Named Nested Relational Calculus (DNNRC)

Translations:

./coq/Translation contains translations between ILs
./coq/Backend contains backend support and code generation
./coq/Frontend contains surface language support (except for jRules)

Toplevel:

./coq/Compiler contains the overall compiler instructure and functional optimizers
./coq/Tests contains various coq-level tests

(./coq/Updates is early code for updates that isn't part of the actual compiler)

