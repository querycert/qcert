# Q\*cert

[![CircleCI](https://circleci.com/gh/querycert/qcert.svg?style=svg)](https://circleci.com/gh/querycert/qcert)

http://github.com/querycert/qcert

## About

This is the source code for Q\*cert, a framework for the development
and verification of query compilers. It supports a rich data model and
a includes a fairly extensive compilation pipeline 'out of the box'.

Q\*cert is built using the Coq proof assistant. A significant subset
of the initial compilation pipeline has been mechanically checked for
correctness.

## Prerequisites

### OCaml and the Coq Proof Assistant

To build Q\*cert from the source, you will need:

 - OCaml 4.02 or later (http://ocaml.org/) along with the following libraries:
  - menhir, a parser generator (http://gallium.inria.fr/~fpottier/menhir/)
  - ocamlbuild, a build system (https://github.com/ocaml/ocamlbuild)
  - camlp5, a pre-processor (http://camlp5.gforge.inria.fr)
 - Coq 8.6 (https://coq.inria.fr/)

An easy way to get set up on most platforms is to use the OCaml
package manager (https://opam.ocaml.org). Once opam is installed, you
can just add the corresponding libraries:

```
opam install menhir
opam install ocamlbuild
opam install camlp5
opam install coq.8.6
opam install js_of_ocaml
```

### Java (Recommended)

SQL, SQL++, and ODM rules support, a part of the Q*cert runtime, and
the harnesses for running the samples, are all written in Java and
require a Java compiler (Java 8 required).  The builds for many of the
Java components also require a recent version of ant (and the ODM
rules support has an additional pre-requisite).  Both the `javac`
command and the `ant` command must be executable from the command line
PATH.

### TypeScript (Optional)

Finally, a Web demo for the compiler is included with the distribution
and requires js_of_ocaml and TypeScript.

js_of_ocaml can be installed as other OCaml packages using opam:

```
opam install js_of_ocaml
```

TypeScript can be obtained from (https://www.typescriptlang.org).

### Portability

Q*cert should build on most recent Linux systems and on MacOS.

Windows isn't directly supported by the OCaml package manager. We do
not currently have detailed instructions for how to build on Windows.

## Building Q\*cert core

### Compile Q*cert

1. Compile the Coq source:

```
make qcert
```

(Note: this will take a while, you can run make faster with `make -j 8 qcert`)

2. Extract the compiler and build the OCaml frontend:

```
make extraction
```

This should produce the `./bin/qcert` and `./bin/qdata` executables.

## Building the Java components

The Java components are built with the command
```
make javacode
```

By default, that command will build the Java runtime and the harnesses
for running the samples, but not the SQL, SQL++, or ODM rules support.
To build the additional components, you must be connected to the
network and must have a copy of ant installed and accessible from the
command line.  The additional components are built by adding make
variable settings to the command line like this:

```
make SQL=yes SQLPP=yes ODM=yes javacode
```

Whichever of these additional components you choose to build, the
selected components should be built together in one step because they
are deployed as a set of interrelated jar files.  After javacode is
built with any of these additional components, the qcert/bin directory
should contain a file called `javaService.jar` and a subdirectory
called `services`.

Note that the ODM rules support will only build if you satisfy an
additional dependency as outlined in the next section.

## Building ODM Rules (JRules) support (Optional)

The ODM rules support requires that you obtain a legal copy of the ODM
Designer component that comes with various versions of ODM.

ODM comes in (at least) two configurations called "ODM Rules" and "ODM
Insights".  Each comes with its own Designer, which in turn supports a
characteristic set of languages.  There are (at least) two license
arrangements: "ODM Classic" has only the Rules configuration and "ODM
Advanced" comes with both Rules and Insights.  There is also ODM in
the cloud, based on the Rules configuration.  We hope that our support
will work with either the Insights Designer or the Rules Designer but
we have only tested it with the Rules Designer and it only covers the
languages that are provided by that Designer.

There is no free version of ODM, but some 30 day free trial programs
will allow you to try out certain versions.  In order to use our
"technical" rule support, you need a binary jar available only with an
ODM Designer.  To use the "designer" rule support, you need to fully
install and utilize an ODM Designer.

One possible route is to sign up for the 30 day free trial of ODM in
the Cloud (https://www.bpm.ibmcloud.com/odm/index.html).  Once you are
authorized for the trial, you can log in to the cloud service and
obtain a copy of the ODM Rules Designer (downloaded and installed on
your own machine).

Once you have a Designer component installed on your machine, the next
step is to find the library called **jrules-engine.jar** and copy it to
a directory in the qcert working tree.  Start by making the directory

```
jrules2CAMP/lib
```

if it does not already exist.

If you installed the Designer using ODM in the cloud, there is a copy
of `jrules-engine.jar` in the `studio/lib` directory of the
directory where the Designer is installed.  Simply copy that file into
the `jrules2CAMP/lib` directory.  If you have some other version of
ODM Rule Designer or Insights Designer, find the location where the
ODM plugins are located and look for a plugin jar whose name starts
with "com.ibm.rules.engine...".  Inside this jar you may find a copy
of jrules-engine.jar.  Unzipping the outer jar into the
`jrules2CAMP` directory should put a copy of jrules-engine.jar in
the `lib` subdirectory.  Beyond those suggestions, you are on your own.


## Compile Queries

Once the compiler is built, it can be used to compile queries. The
[`./samples`](./samples) directory contains a few examples written in OQL (Object
Query Language) syntax. For instance:

```
$ cat samples/oql/persons1.oql 
select p
from p in Customers
where p->age = 32
```

Calling the compiler on that sample with OQL as source language and
Javascript as target language can be done as follows:

```
$ ./bin/qcert -source oql -target js samples/oql/persons1.oql
```

This will tell you the compilation steps being used:

```
Compiling from oql to js:
  oql -> nraenv -> nraenv -> nnrc -> nnrc -> js
```

and produce a JavaScript file called `samples/oql/persons1.js`.

Similarly for Java:

```
$ ./bin/qcert -source oql -target java samples/oql/persons1.oql
```

This will produce a java file called `samples/oql/persons1.java`.

## Run compiled queries

Q\*cert targets a number of languages and data processors as backends
(currently: JavaScript, Java, Cloudant and Spark). The way you run the
compiled queries varies depending on the target. Usually you need two
things: (i) a run-time library that implements some of the core
operators assumed by the compiler (e.g., ways to access records or
manipulate collections), and (ii) a *query runner* which allows to
execute the query on some input data.

Runtime libraries are in the [`./runtime`](./runtime) directory. We include simple
query runners in the [`./samples`](./samples) directory in order to try the examples.

### Prerequisites

The Java runtime library and the sample query runners will have been built if
you followed the instructions above to make the optional Java components
via

```
make javacode
```

Otherwise, you can do it now.

### Run queries compiled to JavaScript

(In the [`./samples`](./samples) directory)

To run a query compiled to JavaScript, you can call `java` for the
`RunJavascript` query runner (It uses uses the Nashorn JavaScript
engine for the JVM). You will need to pass it two pieces of
information: (i) the location of the Q\*cert runtime for JavaScript,
and (ii) some input data on which to run the query. From the command
line, you can do it as follows:

```
java -cp bin:../lib/gson-2.7.jar testing.runners.RunJavascript \
     -input oql/persons.input \
	 -runtime ../runtime/javascript/qcert-runtime.js \
	 oql/persons1.js
```

The input data in [`data/persons.json`](./samples/data/persons.json)
contains a collection of persons and a collection of companies in JSON
format and can be used for all the tests. If you run persons1, it should
return all persons whose age is 32:

```
[{"pid":1,"name":"John Doe","age":32,"company":101},
 {"pid":2,"name":"Jane Doe","age":32,"company":103},
 {"pid":4,"name":"Jill Does","age":32,"company":102}]
```

Alternatively the provided [`./samples/Makefile`](./samples/Makefile)
can compile and run a given test for you:

```
make run_js_persons1
```
### Run queries compiled to Java

(In the [`./samples`](./samples) directory)

To run a query compiled to Java, you must first compile it by calling
`javac` for the produced Java code, then call `java` with the
`RunJava` query runner. You will need to pass it three pieces of
information: (i) the location of the gson jar which is used to parse
the input, (ii) the location of the Q\*cert runtime for Java, both as
part of the classpath, and (ii) some input data on which to run the
query. From the command line, you can do it as follows, first to
compile the Java code:

```
javac -cp bin:../runtime/java/bin:../lib/gson-2.7.jar oql/persons1.java
```

Then to run the compiled Class:

```
java -cp bin:../runtime/java/bin:../lib/gson-2.7.jar:oql testing.runners.RunJava \
     -input oql/persons.input \
	 persons1
```

Alternatively the provided [`./samples/Makefile`](./samples/Makefile)
can compile and run a given test for you:

```
make run_java_persons1
```

## Spark Dataset backend

To compile the Spark runtime and run queries on Spark you need `sbt`
and `spark-submit` on your path.

- [sbt](http://www.scala-sbt.org/)
- [Spark](https://spark.apache.org/)

Currently there is only one Spark example. You can compile and run it like this:

```
make spark2-runtime
cd tests/spark2/
./run.sh
```


## Caveats

- There is no official support for Windows, although some success has been reported (See [Issue #1](https://github.com/querycert/qcert/issues/1))
- The Spark 2 target is in development, and not yet operational
- The documentation is based on an early version of the compiler and is outdated
- Support for the source miniOQL language is preliminary


## Code Organization

The code is in three main directories:
- [`./coq`](./coq) contains the Coq source code
- [`./ocaml`](./ocaml) contains the toplevel compiler and code extraction from Coq
- [`./runtime`](./runtime) contains libraries necessary to run queries compiled through Q*cert for various platforms (Java, JavaScript, and Spark 2.0).

Inside the [`./coq`](./coq) directory, the organization is as follows.
- Foundational modules:
  - [`./Basic/Util`](./coq/Basic/Util) contains useful libraries and lemmas, independant of Q*cert itself
  - [`./Basic/Data`](./coq/Basic/Data) contains the core data model
  - [`./Basic/Operators`](./coq/Basic/Operators) contains unary/binary operators shared across ILs
  - [`./Basic/TypeSystem`](./coq/Basic/TypeSystem) contains the core type system
  - [`./Basic/Typing`](./coq/Basic/Typing) contains typing and type inference for data and operators
- Intermediate languages (ILs), including eval, typing, type inference, and equivalences/rewrites:
  - [`./CAMP`](./coq/CAMP) contains support for the Calculus of Aggregating Matching Patterns
  - [`./NRA`](./coq/NRA) contains support for the Nested Relational Algebra
  - [`./NRAEnv`](./coq/NRAEnv) contains support for the extension of NRA with environments
  - [`./NNRC`](./coq/NNRC) contains support for the Named Nested Relational Calculus
  - [`./NNRCMR`](./coq/NNRCMR) contains support for the Named Nested Relational Calculus with Map-Reduce
  - [`./DNNRC`](./coq/DNNRC) contains support for the Distributed Named Nested Relational Calculus
- Translations:
  - [`./Translation`](./coq/Translation) contains translations between ILs
  - [`./Backend`](./coq/Backend) contains backend support and code generation
  - [`./Frontend`](./coq/Frontend) contains surface language support (except for jRules)
- Toplevel:
  - [`./Compiler`](./coq/Compiler) contains the overall compiler instructure and functional optimizers
  - [`./Tests`](./coq/Tests) contains various coq self-tests
  - ([`./Updates`](./coq/Updates) is early code for updates that isn't part of the actual compiler)

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

- JavaScript [JS06], Java [Java7], Cloudant (CouchDB), and Spark
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


