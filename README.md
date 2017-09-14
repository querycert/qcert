# Q\*cert

[![CircleCI](https://circleci.com/gh/querycert/qcert.svg?style=svg)](https://circleci.com/gh/querycert/qcert)

Git: http://github.com/querycert/qcert

Web Site: http://querycert.github.io


## About

This is the source code for Q\*cert, a framework for the development
and verification of query compilers. It supports a rich data model and
includes an extensive compilation pipeline 'out of the box'.

Q\*cert is built using the Coq proof assistant
(https://coq.inria.fr). A significant subset of the provided
compilation pipeline has been mechanically checked for correctness.


## Prerequisites

### OCaml and the Coq Proof Assistant

To build Q\*cert from the source, you will need:

- OCaml 4.05.0 or later (http://ocaml.org/) along with the following libraries:
  - ocamlbuild, a build system (https://github.com/ocaml/ocamlbuild)
  - menhir, a parser generator (http://gallium.inria.fr/~fpottier/menhir/)
  - camlp5, a pre-processor (http://camlp5.gforge.inria.fr)
  - base64, a library for base64 encoding and decoding (https://github.com/mirage/ocaml-base64)
  - js\_of\_ocaml, a compiler from OCaml to JavaScript
- Coq 8.6.1 (https://coq.inria.fr/)

An easy way to get set up on most platforms is to use the OCaml
package manager (https://opam.ocaml.org). Once opam is installed, you
can just add the corresponding libraries:

```
opam install ocamlbuild menhir camlp5 base64 js_of_ocaml js_of_ocaml-ppx
opam install coq.8.6.1
```

### Java (Recommended)

Parsers for SQL, SQL++, and ODM rules, parts of the Q\*cert runtime,
as well as utilities for running compiled queries are written in Java
and require a Java 8 compiler.

Building those Java components also requires a recent version of ant
(and the ODM rules support has additional pre-requisites).

Both the `javac` and the `ant` executables must be available from the
command line.

### Scala (Optional)

The Spark targets require a Scala compiler and the Scala Build Tool
(sbt).

Scala can be obtained from: https://www.scala-lang.org.

sbt can be obtained from: http://www.scala-sbt.org.

### TypeScript (Optional)

The Q\*cert distribution includes a Web demo for the compiler which
is written in TypeScript.

TypeScript can be obtained from: https://www.typescriptlang.org.

### Portability

Q\*cert should build on most recent Linux systems and on MacOS.

Windows isn't directly supported by the OCaml package manager. We do
not currently have detailed instructions for how to build on Windows.


## Getting started

### Build the compiler

To compile Q*cert from the source, do:

```
make
```

(Note: this will take a while, you can run make faster with `make -j 8`)

If all goes well, this should:
- Build the compiler itself (the executable `bin/qcert`)
- Build the supporting parsers in Java for SQL and SQL++ (a jar file
called `bin/javaService.jar` and a subdirectory called `bin/services`
containing dependencies)
- Build the Q\*cert runtime libraries for JavaScript and Java (in
  `runtimes`)
- Build sample query runners in Java in order to run the queries (a
  jar file called `bin/javaRunners.jar` and a subdirectory called
  `bin/lib` containing dependencies)

By default, this assumes you have Java and ant installed, and an
internet connection (needed the first time you do `make` in order to
download the libraries needed for the Java part of the code). If you
want or need to change the default configuration (e.g., you do not
have Java installed, want to build support for Spark, etc), consult
the detailed instructions below.

For instance:

```
$ cat samples/oql/persons1.oql 
select p
from p in Customers
where p->age = 32
```

Calling the compiler on that sample with OQL as source language and
JavaScript as target language can be done as follows:

```
$ ./bin/qcert -source oql -target js samples/oql/persons1.oql
```

This will tell you the compilation steps being used:

```
Compiling from oql to js:
  oql -> nraenv -> nraenv -> nnrc -> nnrc -> js
```

and produce a JavaScript file called `samples/oql/persons1.js`.


### Compile a query

Once the compiler is built, you can try it on a sample query, for
instance:

```
$ cat samples/oql/persons1.oql 
select p
from p in Customers
where p->age = 32
```

Calling the compiler on that sample with OQL as source language and
JavaScript as target language can be done as follows:

```
$ ./bin/qcert -source oql -target js samples/oql/persons1.oql
```

This will tell you the compilation steps being used:

```
Compiling from oql to js:
  oql -> nraenv -> nraenv -> nnrc -> nnrc -> js
```

and produce a JavaScript file called `samples/oql/persons1.js`.


### Run a compiled query

To run a query compiled to JavaScript, you can call `java` for the
`RunJavascript` query runner (It uses uses the Nashorn JavaScript
engine for the JVM). You will need to pass it two pieces of
information: (i) the location of the Q\*cert runtime for JavaScript,
and (ii) some input data on which to run the query. From the command
line, you can do it as follows:

```
cd samples
java -cp ../bin/*:../bin/lib/* testing.runners.RunJavascript \
     -input oql/persons.input \
	 -runtime ../runtimes/javascript/qcert-runtime.js \
	 oql/persons1.js > oql/persons1.out 
```

The input data in [`data/persons.json`](./samples/data/persons.json)
contains a collection of persons and a collection of companies in JSON
format. If you run persons1, it should return all persons whose age is
32:

```
[{"pid":1,"name":"John Doe","age":32,"company":101},
 {"pid":2,"name":"Jane Doe","age":32,"company":103},
 {"pid":4,"name":"Jill Does","age":32,"company":102}]
```

## Build configuration

The build relies on a small configuration file, which controls what
source and target languages should be supported:

```
Makefile.config
```

You can edit that file, which by default assumes you have Java and Ant
installed and attempts to build the SQL and SQL++ support, as well as
the Java runtime.

You can also override the configuration from the command line to build
specific components, for instance, to build only for JavaScript:

```
make SQL= SQLPP= JAVA=
```

To add support for all sources and target languages, including ODM
rules and Spark:

```
make JRULES=yes SPARK=yes
```

Note that the ODM rules support will only build if you satisfy an
additional dependency as outlined in [README-ODM](README-ODM.md).

Whichever of these components you choose to build, they should be
built together in one step because some of the Java components are
deployed as a set of interrelated jar files.

## Cleaning up

If you want to rebuild the compiler from scratch, first clean up by
calling:

```
make clean
```

or, if you also want to remove the external (Java dependencies) that
may have downloaded, by calling:

```
make cleanall
```

## Building the Web demo

To compile the web demo, do:

```
make demo
```

Once, compiler, the Web demo can be started by opening the following
HTML page:

```
doc/demo/demo.html
```

If you want support for any of the optional source languages (SQL,
SQL++ and ODM rules) in the demo, you will also need to run the
javaService as follows:

```
cd bin; java -jar javaService.jar -server 9879
```

## Documentation

Code documentation and background information, notably references for
all supported languages, can be found on the Q*cert Web site:
https://querycert.github.io

If you want to re-generated the documentation from the source itself,
you will need to install the
[coq2html](https://github.com/xavierleroy/coq2html) tool. Detailed
instructions are provided in [./doc/README.md](./doc/README.md)


## Using Q\*cert

### Compiling Queries

The `./bin/qcert` can simply be called by giving a source and target
language. For instance, to compile the sample query
`samples/sql/org2.sql` from SQL to Java, do:

```
./bin/qcert -source sql -target java samples/sql/org2.sql

```

The compiler will always list the chosen compilation path:

```
Compiling from sql to java:
  sql -> nraenv -> nraenv -> nnrc -> nnrc -> java
```

A list of all the available languages, along with options for the
compiler can be found from the command line:

```
./bin/qcert -help
```

### Running the compiled queries

#### Run queries compiled to JavaScript

(In the [`./samples`](./samples) directory)

To run a query compiled to JavaScript, you can call `java` for the
`RunJavascript` query runner (It uses uses the Nashorn JavaScript
engine for the JVM). You will need to pass it two pieces of
information: (i) the location of the Q\*cert runtime for JavaScript,
and (ii) some input data on which to run the query. From the command
line, you can do it as follows:

```
cd samples
java -cp ../bin/*:../bin/lib/* testing.runners.RunJavascript \
     -input oql/persons.input \
	 -runtime ../runtimes/javascript/qcert-runtime.js \
	 oql/persons1.js > oql/persons1.out 
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
#### Run queries compiled to Java

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
javac -cp ../runtimes/java/bin:../bin/lib/* oql/persons1.java
```

Then to run the compiled Class:

```
java -cp ../runtimes/java/bin:../bin/*:../bin/lib/*:oql testing.runners.RunJava \
     -input oql/persons.input \
	 persons1
```

Alternatively the provided [`./samples/Makefile`](./samples/Makefile)
can compile and run a given test for you:

```
make run_java_persons1
```

#### Spark Dataset backend

We provide a Spark example in `samples/spark2`. To compile and run it, do:

```
make spark2-runtime
cd samples/spark2/
./run.sh
```


## Caveats

- There is no official support for Windows, although some success has been reported using Cygwin
- The Spark 2 target is under development
- Some of the source languages are only partially supported
- Only part of the compilation pipeline has been mechanically verified for correctness


## License

Q\*cert is distributed under the terms of the Apache 2.0 License, see `./LICENSE.txt`

## Contributions

Q\*cert is still at an early phase of development and we welcome
contributions. Contributors are expected to submit a 'Developer's
Certificate of Origin' which can be found in ./DCO1.1.txt.

