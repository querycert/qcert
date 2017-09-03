# Q\*cert

[![CircleCI](https://circleci.com/gh/querycert/qcert.svg?style=svg)](https://circleci.com/gh/querycert/qcert)

http://github.com/querycert/qcert

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
opam install ocamlbuild
opam install menhir
opam install camlp5
opam install base64
opam install js_of_ocaml js_of_ocaml-ppx
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

The Q\*cert compile can generate code for Spark execution which
requires a Scala compiler and the Scala Build Tool (sbt).

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

## Installing Q\*cert

### Configuration

Copy the provided configuration template:

```
cp Makefile.config_tmpl Makefile.config
````

The default configuration assumes you have Java and Ant installed and
attempt to build the SQL and SQL++ support. Additional configuration
parameters can be set to support other source languages (e.g., ODM
rules) and backends (e.g., Spark).

### Building the compiler

To compile Q*cert from the source, do:

```
make qcert
```

(Note: this will take a while, you can run make faster with `make -j 8 all`)

This should produce the `qcert` and `qdata` executables in the `./bin`
directory.

If configured for SQL or SQL++, it should also produce a file called
`javaService.jar` and a subdirectory called `services` in the `./bin`
directory.

You can override the configuration from the command line to build
specific components, for instance:

```
make SQL=yes SQLPP=yes JRULES=yes qcert
```

Whichever of these additional components you choose to build, the
selected components should be built together in one step because they
are deployed as a set of interrelated jar files.

Note that the ODM rules support will only build if you satisfy an
additional dependency as outlined in README-ODM.md.

### Building the Q\*cert runtimes

To run the compiled queries, you will also need a small
target-specific runtime (e.g., for JavaScript, Java or Spark).

To build the runtimes, do:

```
make qcert-runtimes
```

You can override the configuration from the command line to build
specific components, for instance:

```
make SPARK=yes qcert-runtimes
```

### Building the Web demo (Optional)

To compile the web demo, do:

```
make demo
```

If you have built Q*cert for any of the optional source languages
(SQL, SQL++ and ODM rules), you will need to run the javaService as
follows:

```
cd bin
java -jar javaService.jar -server 9879
```

The Web demo can be started by opening the following HTML page:

```
webdemo/demo.html
```

A simple version for development purposes can be started by opening the following HTML page:

```
webdemo/qcert.html
```

## Using Q\*cert

### Compiling Queries

The [`./samples`](./samples) directory contains a few examples written
in OQL (Object Query Language) syntax. For instance:

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

Similarly for Java:

```
$ ./bin/qcert -source oql -target java samples/oql/persons1.oql
```

This will produce a java file called `samples/oql/persons1.java`.

### Running the compiled queries

We include simple query runners in the [`./samples`](./samples)
directory in order to try the examples.

#### Build the query runners

To build the query runners, do:

```
make qcert-runners
```

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
java -cp bin:lib/* testing.runners.RunJavascript \
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
javac -cp ../runtime/java/bin:bin:lib/* oql/persons1.java
```

Then to run the compiled Class:

```
java -cp ../runtime/java/bin:bin:lib/*:oql testing.runners.RunJava \
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

## Documentation

Code documentation and background information can be found at: https://querycert.github.io


## Caveats

- There is no official support for Windows, although some success has been reported using Cygwin
- The Spark 2 target is under development
- Some of the source languages are only partially supported


## License

Q\*cert is distributed under the terms of the Apache 2.0 License, see `./LICENSE.txt`

## Contributions

Q\*cert is still at an early phase of development and we welcome
contributions. Contributors are expected to submit a 'Developer's
Certificate of Origin' which can be found in ./DCO1.1.txt.

