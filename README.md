# Q\*cert

http://github.com/querycert/qcert

## About

This is the source code for the Q\*cert certified query compiler. The
goal of the project is to develop a state of the art query compiler
for languages over a rich data model (nested, hierarchical, etc), with
an implementation which provides strong correctness guarantees.

Q\*cert is built and verified using the Coq proof assistant. A working
compiler can be obtained by 'extracting' OCaml code from the source
in Coq.

## Building Q\*cert

### Prerequisites

To build Q\*cert from the source, you will need:

 - OCaml 4.01 or later (http://ocaml.org/) along with the following libraries:
  - ocamlbuild, a build system (https://github.com/ocaml/ocamlbuild)
  - menhir, a parser generator (http://gallium.inria.fr/~fpottier/menhir/)
  - camlp5, a pre-processor (http://camlp5.gforge.inria.fr)
 - Coq 8.5pl1 or later (https://coq.inria.fr/)

An easy way to get set up on most platforms is to use the OCaml
package manager (https://opam.ocaml.org). Once opam is installed, you
can just add the corresponding libraries:

```
opam install ocamlbuild
opam install menhir
opam install camlp5
opam install coq
```

One platform that isn't directly supported by the OCaml package
manager is Windows. We do not currently have detailed instructions for
how to build on Windows.

### Compile Q*cert

1. Compile the Coq source:

	make qcert
	(Note: this will take a while, you can run make faster with 'make -j 8 qcert')

2. Extract the compiler and build the OCaml frontend:

	make extraction

This should produce the following executables in the ./bin directory:
CACo for the Q\*cert compiler, CAEv for the Q\*cert evaluator, and
CADa for the Q\*cert data processor.

## Compile Queries

Once the compiler is built, one can use it to compile queries. The
`samples` directory contains a few examples written in OQL (Object
Query Language) syntax. For instance:

```
$ cat samples/oql/test1.oql 
select p
from p in Persons
where p.age = 32
```

Calling the compiler on that sample with OQL as source language and
Javascript as target language can be done as follows:

```
$ ./bin/CACo -source OQL -target JS samples/oql/test1.oql
```

This will produce a javascript file called `samples/oql/test1.js`.

Similarly for Java:

```
$ ./bin/CACo -source OQL -target Java samples/oql/test1.oql
```

This will produce a java file called `samples/oql/test1.java`.

## Run compiled queries

Q\*cert targets a number of languages and data processors as backends
(currently: Javascript, Java, Cloudant and Spark). The way you run the
compiled queries varies depending on the target. Usually you need two
things: (i) a run-time library that implements some of the core
operators assumed by the compiler (e.g., ways to access records or
manipulate collections), and (ii) a *query runner* which allows to
execute the query on some input data.

Runtime libraries are in the ./runtime directory. We include simple
query runners in the .samples directory in order to try the examples.

### Prerequisites

To compile the Java runtime library or the provided query runner, you
will need a Java compiler (Java 7 or later).

### Build the Q\*cert runtimes

To compile the supporting runtime for the Java target:

```
make java-runtime
```

## Caveats

- The Spark 2 target is not operational
- The documentation is based on an early version of the compiler and is outdated
- Support for the source miniOQL language is very preliminary


## Code Organization

The code is in three main directories:
- [`./coq`](./coq) contains the Coq source code
- [`./ocaml`](./ocaml) contains the toplevel compiler and code extraction from Coq
- [`./runtime`](./runtime) contains libraries necessary to run queries compiled through Q*cert for various platforms (Java, Javascript, and Spark 2.0).

Inside the [`./coq`](./coq) directory, the organization is as follows.
- Foundational modules:
  [`./Basic/Util`](./coq/Basic/Util) contains useful libraries and lemmas, independant of Q*cert itself
  [`./Basic/Data`](./coq/Basic/Data) contains the core data model
  [`./Basic/Operators`](./coq/Basic/Operators) contains unary/binary operators shared across ILs
  [`./Basic/TypeSystem`](./coq/Basic/TypeSystem) contains the core type system
  [`./Basic/Typing`](./coq/Basic/Typing) contains typing and type inference for data and operators
- Intermediate languages (ILs), including eval, typing, type inference, and equivalences/rewrites:
  [`./CAMP`](./coq/CAMP) contains support for the Calculus of Aggregating Matching Patterns (CAMP)
  [`./NRA`](./coq/NRA) contains support for the Nested Relational Algebra (NRA)
  [`./NRAEnv`](./coq/NRAEnv) contains support for the extension of NRA with environments
  [`./NNRC`](./coq/NNRC) contains support for the Named Nested Relational Calculus (NNRC)
  [`./DNNRC`](./coq/DNNRC) contains support for the Distributed Named Nested Relational Calculus (DNNRC)
- Translations:
  [`./Translation`](./coq/Translation) contains translations between ILs
  [`./Backend`](./coq/Backend) contains backend support and code generation
  [`./Frontend`](./coq/Frontend) contains surface language support (except for jRules)
- Toplevel:
  [`./Compiler`](./coq/Compiler) contains the overall compiler instructure and functional optimizers
  [`./Tests`](./coq/Tests) contains various coq self-tests
  ([`./Updates`](./coq/Updates) is early code for updates that isn't part of the actual compiler)

## License

Q*cert is distributed under the terms of the Apache 2.0 License, see `./LICENSE.txt`

## Contributions

Q*cert is still at an early phase of development and we welcome
contributions. Contributors are expected to submit a 'Developer's
Certificate of Origin' which can be found in ./DCO1.1.txt.

## Background

Current source languages include:

- mini-OQL [SS16], a usable query language for objects, which is
  a subset of OQL [ODMG30].

Current targets include:

- Javascript [JS06], Java [Java7], Cloudant (CouchDB), and Spark
  [Zah12].

The compiler relies a number of intermediate languages for
optimization and code-generation, notably:

A calculus for pattern-matching with aggregation:

- We use the Calculus of Aggregating Matching Patterns (CAMP)
  from [SSH15] to capture the pattern matching and data
  processing semantics of rules languages, such as jRules [BM11]

A nested-relational algebra:

- We use the nested relational algebra (NRA) from [Clu93,Moe09],
  which is designed for optimization purposes. It includes the
  relational algebra as a subset and has been applied
  successfully to a variety of query languages, notably OQL and
  XQuery.

A nested-relational calculus:

- We use the Named Nested Relational Calculus (NNRC) from
  [Bus07], which makes the encoding of NRA operators natural, and
  is closely related to the 'XQuery core' used in [FSW01], and
  comprehensions.

The compiler includes translations from source to target and an
optimizer which leverages the database algebra and calculus. Those
translations, as well as the optimization rules are proved correct
using the Coq proof assistant.


## References

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
K. Barry. Vol. 1. San Francisco: Morgan Kaufmann, 2000. http://www.odbms.org/odmg-standard/odmg-book/

[SSH15] Avraham Shinnar, Jérôme Siméon, and Martin Hirzel. "A Pattern
Calculus for Rule Languages: Expressiveness, Compilation, and
Mechanization." 29th European Conference on Object-Oriented
Programming. 2015. http://hirzels.com/martin/papers/ecoop15-rules-nra.pdf

[SS16] Avraham Shinnar and Jérôme Siméon. "Nominal Typing for Data
Languages". Technical Report, IBM. July 2016

[Zah12] Matei Zaharia, et al. "Fast and interactive analytics over
Hadoop data with Spark." USENIX; login 37.4 (2012): 45-51. https://www.usenix.org/publications/login/august-2012-volume-37-number-4/fast-and-interactive-analytics-over-hadoop-data


