<h1 align="center">Q*cert</h1>

<p align="center">
  <a href="https://circleci.com/gh/querycert/qcert"><img src="https://circleci.com/gh/querycert/qcert.svg?style=shield" alt="Build Status"></a>
  <a href="./LICENSE"><img src="https://img.shields.io/github/license/accordproject/ergo?color=bright-green" alt="License"></a>
  <a href="https://www.npmjs.com/package/qcert"><img src="https://img.shields.io/npm/dm/qcert" alt="downloads"></a>
  <a href="https://badge.fury.io/js/qcert"><img src="https://badge.fury.io/js/qcert.svg" alt="npm version"></a>
</p>

## About

This is the source code for Q\*cert, a framework for the development and verification of domain specific languages. It supports a rich data model and includes an extensive compilation pipeline 'out of the box'. Applications include query languages (e.g., SQL, OQL), rules languages (e.g., JRules) and smart contract languages (e.g., Ergo).

Q\*cert is built with the Coq proof assistant (https://coq.inria.fr). A significant subset of the provided compilation pipeline has been mechanically checked for correctness.

## Installation with Opam

The simplest way to install Q*cert is through opam:

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-qcert
```

## Installation from Source

### Prerequisites

#### OCaml and the Coq Proof Assistant

To build Q\*cert from the source, you will need:

- OCaml 4.09.1 or later (http://ocaml.org/) along with the following libraries:
  - dune, a build system (https://dune.build)
  - menhir, a parser generator (http://gallium.inria.fr/~fpottier/menhir/)
  - base64, a library for base64 encoding and decoding (https://github.com/mirage/ocaml-base64)
  - js\_of\_ocaml (along with the library js\_of\_ocaml-ppx), a compiler from OCaml to JavaScript
  - re, a pure OCaml library for regular expressions
  - calendar, a library for manipulating date and time
  - uri, a library for processing URIs
  - wasm, a WebAssembly reference interpreter
- Coq 8.15.1 or later (https://coq.inria.fr/) along with the following libraries:
  - jsast, a minimal AST for JavaScript

An easy way to get set up on most platforms is to use the OCaml package manager (https://opam.ocaml.org). Once opam is installed, you can just add the corresponding libraries:

```
$ opam repo add coq-released https://coq.inria.fr/opam/released
$ opam install . --deps-only
```

*Warning:* It seems that coq and/or the Q\*cert build process does not like opam local switches.
If you want to use a separate opam switch for Q\*cert, we recommend creating a new named global switch *before* executing the above steps.

```
$ opam switch create qcert 4.09.1
```

#### Node.js (Recommended)

Execution and testing for the JavaScript compilation target, as well demo material, requires Node.js. We suggest Node.js version 10 or 12.

Node.js can be installed from https://nodejs.org/en/

#### Java (Recommended)

Parsers for SQL, SQL++, and ODM rules, the Q\*cert runtime for the Java compilation target, as well as utilities for running compiled queries are written in Java and require a Java 8 compiler.

Building those Java components also requires a recent version of ant (and the ODM rules support has additional pre-requisites).

Both the `javac` and the `ant` executables must be available from the command line.

#### Scala (Optional)

The Spark compilation target requires a Scala compiler and the Scala Build Tool (sbt).

Scala can be obtained from: https://www.scala-lang.org.

sbt can be obtained from: http://www.scala-sbt.org.

### Portability

Q\*cert should build on most recent Linux systems and on MacOS.

We do not currently have detailed instructions for how to build on Windows.


### Build the compiler from Source

To compile Q\*cert from the source, do:

```
$ make
```

(Note: this will take a while, you can run make faster with `make -j 8`)

If all goes well, this should:
- Build the compiler itself (the executable `bin/qcert`)
- Build the supporting parsers in Java for SQL and SQL++ (a jar file called `bin/javaService.jar` and a subdirectory called `bin/services` containing dependencies)
- Build the Q\*cert runtime libraries for JavaScript and Java (in `runtimes`)
- Build sample query runners in Java in order to run the queries (a jar file called `bin/javaRunners.jar` and a subdirectory called `bin/lib` containing dependencies)

By default, this assumes you have Java and ant installed, and an internet connection (needed the first time you do `make` in order to download the libraries needed for the Java part of the code). If you want or need to change the default configuration (e.g., you do not have Java installed, want to build support for Spark, etc), consult the instructions for the [Build Configuration](#build-configuration) below.


### Compile a query

Once the compiler is built, you can try it on a sample query, for instance:

```
$ cat tests/oql/persons1.oql 
/* Simple select-from-where */
select p
from p in Customers
where p->age = 32
```

Calling the compiler on that OQL query with JavaScript as target language can be done as follows:

```
$ bin/qcert -source oql -target js -schema tests/oql/persons.schema tests/oql/persons1.oql
```

which should produce a JavaScript file called `tests/oql/persons1.js`.


### Run that compiled query

To run the resulting JavaScript, you can use the provided node CLI.

You will need to pass it the following: (i) the compiled query (`tests/oql/persons1.js` in our example), (ii) the schema for that query, (iii) some input data. From the command line, you can do it as follows:

```
$ node cli/nodejs/bin/qcertRun.js execute \
       --input tests/oql/persons.input \
       --schema tests/oql/persons.schema \
       --query tests/oql/persons1.js
```

The input data in [`tests/oql/persons.input`](tests/oql/persons.input) contains a collection of persons and a collection of companies in JSON format. If you run persons1, it should return all persons whose age is 32:

```
[ { "$class": ["Customer"], "$data": { "name": "John Doe", "age": { "$nat": 32 }, "cid": { "$nat": 123 } } }, 
  { "$class": ["Customer"], "$data": { "name": "Jane Doe", "age": { "$nat": 32 }, "cid": { "$nat": 124 } } }, 
  { "$class": ["Customer"], "$data": { "name": "Jill Does", "age": { "$nat": 32 }, "cid": { "$nat": 126 } } } ]
```


## Build configuration

The build relies on a small configuration file in the toplevel directory called ```Makefile.config```. This file controls what source and target languages should be supported. By default the configuration
assumes you have Java and Ant installed and attempts to build the SQL and SQL++ support, as well as the Java runtime.

You can edit that file by commenting out the languages you want or commenting those you don't want. Alternatively, you can override the configuration from the command line to build specific components, for instance, to build without any Java support (i.e., only for JavaScript):

```
$ make SQL= SQLPP= JAVA=
```

To add support for all source and target languages, including ODM rules and Spark:

```
$ make JRULES=yes SPARK=yes
```

Note that the ODM rules support will only build if you satisfy an additional dependency as outlined in [README-ODM](README-ODM.md).

Whichever of these components you choose to build, they should be built together in one step because some of the Java components are deployed as a set of interrelated jar files.


## Cleaning up

If you want to rebuild the compiler from scratch, first do a clean up by calling:

```
$ make clean
```

You can also force the removal of all external Java libraries as part of that cleanup, by calling:

```
$ make cleanall
```


## Building the Web demo

To compile the web demo, do:

```
$ make demo
```

Once compiled, the Web demo can be started by opening the following
HTML page:

```
documentation/demo/demo.html
```

If you want support for any of the optional source languages (SQL, SQL++ and ODM rules) in the demo, you will also need to run the javaService as follows:

```
$ cd bin; java -jar javaService.jar -server 9879
```

## Documentation

Code documentation and background information, notably references for all supported languages, can be found on the Q\*cert Web site: https://querycert.github.io

If you want to re-generated the documentation from the source itself, you will need to install [coq2html](https://github.com/xavierleroy/coq2html). Detailed instructions are provided in [doc/README.md](documentation/README.md)

## Using Q\*cert

### Command line help

Q\*cert supports many languages. A list of all the available languages, along with a description of the command-line options for the compiler can be obtained by calling:

```
$ bin/qcert -help
```

The list includes source query languages, target languages, and intermediate languages.

### Specifying the source and target

The simplest way to call the compiler is by simply providing a source and target language.

For instance, compiling from SQL to JavaScript (on the example query `tests/sql/org2.sql`) can be done by calling:

```
$ bin/qcert -source sql -target javascript -schema tests/sql/org.schema tests/sql/org2.sql
```

Compiling from λ-NRA to Java (on the example query `tests/lambda_nra/persons6.lnra`) can be done by calling:

```
$ bin/qcert -source lambda_nra -target java -schema tests/lambda_nra/persons.schema tests/lambda_nra/persons6.lnra
```

By default the compiled code will be placed in the same directory as your input query (in this example in `tests/lambda_nra/persons6.java`).

You can change the target directory by using the `-dir` option on the command line, for instance:

```
$ bin/qcert -source lambda_nra -target java -schema tests/lambda_nra/persons.schema -dir . tests/lambda_nra/persons6.lnra
```

You can also compile multiple queries at once, for instance:

```
$ bin/qcert -source oql -target javascript -schema tests/oql/persons.schema tests/oql/persons*.oql
```


### Specifying the compilation path

When compiling from source to target, Q\*cert choses a default compilation path. The compilation path that is being used is always printed out. For instance, if you compile the same SQL example as above to `nnrc_core (Core Named Nested Relational Calculus), you should see:

```
$ bin/qcert -source sql -target nnrc_core -schema tests/sql/org.schema tests/sql/org2.sql
Compiling from sql to nnrc_core:
  sql -> nraenv -> nraenv -> nnrc -> nnrc -> nnrc_core
```

When the path indicates the same intermediate language twice in a row it means an optimization pass has been used. Here optimization has been performed on both `nraenv` (Nested Relational Algebra with Environments) and `nnrc` (Named Nested Relational Calculus).

You can force the use of a specific intermediate language by using the `-path` option on the command line, for instance:

```
$ bin/qcert -source sql -path nraenv_core -target nnrc_core -schema tests/sql/org.schema tests/sql/org2.sql
Compiling from sql to nnrc_core:
  sql -> nraenv -> nraenv -> nraenv_core -> nraenv -> nraenv -> nnrc -> nnrc -> nnrc_core
```

You can also fully specify the compilation path by using the `-exact-path` option on the command line, for instance:

```
$ bin/qcert -exact-path -source sql -path nraenv -path nraenv_core -target nnrc_core -schema tests/sql/org.schema tests/sql/org2.sql
Compiling from sql to nnrc_core:
  sql -> nraenv -> nraenv_core -> nnrc_core
```

If the specified path does not exist, the compiler will return a compilation error:

```
$ bin/qcert -exact-path -source sql -path nraenv -target javascript -schema tests/sql/org.schema tests/sql/org2.sql
Compiling from sql to js:
  sql -> nraenv -> js
Fatal error: exception Util.Qcert_Error("In file [tests/sql/org2.sql] Cannot compile to error (No compilation path from nraenv to js)")
```

### Reference semantics

All of the intermediate languages, and some of the source languages (OQL and λ-NRA) are accompanied by an executable semantics written in Coq which can serve as a reference.

You can get the result of a query according to that reference semantics by using the `-eval` option on the command line, along with the `-input` option to specify a JSON input. For instance, the reference semantics for the λ-NRA example `tests/lambda_nra/persons6_lambda_nra.json` on the input data in `tests/lambda_nra/persons.input` can be obtained by calling:

```
$ bin/qcert -source lambda_nra -target lambda_nra tests/lambda_nra/persons6.lnra \
            -eval -schema tests/lambda_nra/persons.schema -input tests/lambda_nra/persons.input 
Compiling from lambda_nra to lambda_nra:
  lambda_nra
$ cat tests/lambda_nra/persons6_lambda_nra.json 
["John Doe", "Jane Doe", "Jill Does"]
```

The reference semantics for that same example after compilation to the Named Nested Relational Calculus can be obtained by calling:

```
$ bin/qcert -source lambda_nra -target nnrc -schema tests/lambda_nra/persons.schema \
            -eval -input tests/lambda_nra/persons.input tests/lambda_nra/persons6.lnra
Compiling from lambda_nra to nnrc:
  lambda_nra -> nraenv -> nraenv -> nnrc -> nnrc
$ cat tests/lambda_nra/persons6_nnrc.json 
["John Doe", "Jane Doe", "Jill Does"]
```

You can also get the reference semantics for all the languages on the compilation path by using the `-eval-all` option on the command line:

```
$ bin/qcert -source lambda_nra -target nnrc -schema tests/lambda_nra/persons.schema \
            -eval -input tests/lambda_nra/persons.input -eval-all tests/lambda_nra/persons6.lnra
Compiling from lambda_nra to nnrc:
  lambda_nra -> nraenv -> nraenv -> nnrc -> nnrc
$ cat tests/lambda_nra/persons6_lnra_nraenv.json 
["John Doe", "Jane Doe", "Jill Does"]
$ cat tests/lambda_nra/persons6_lnra_nraenv_nraenv.json 
["John Doe", "Jane Doe", "Jill Does"]
```


## Target specific information

How to use or run the compiled code can vary greatly depending on the target language. Facilitating the use of the resulting code and supporting a broader range of targets is still an area of active work.

We welcome comments and suggestions (please use the [Q\*cert github issue tracker](https://github.com/querycert/qcert/issues)). Below are some initial target-specific guidelines.


### JavaScript Target

To run a query compiled to JavaScript, you can call the `qcertRun` executable for Node.js. You will need to pass it three pieces of information: (i) the compiled query (`tests/oql/persons1.js` in our example), (ii) the schema for that query, (iii) some input data. From the command line, you can do it as follows:

```
$ node clis/nodejs/bin/qcertRun.js execute \
       --input tests/oql/persons.input \
       --schema tests/oql/persons.schema \
       --query tests/oql/persons1.js
```

The input data in [`tests/oql/persons.input`](tests/oql/persons.input) contains a collection of persons and a collection of companies in JSON format. If you run persons1, it should return all persons whose age is 32:

```
[ { "$class": ["Customer"], "$data": { "name": "John Doe", "age": { "$nat": 32 }, "cid": { "$nat": 123 } } }, 
  { "$class": ["Customer"], "$data": { "name": "Jane Doe", "age": { "$nat": 32 }, "cid": { "$nat": 124 } } }, 
  { "$class": ["Customer"], "$data": { "name": "Jill Does", "age": { "$nat": 32 }, "cid": { "$nat": 126 } } } ]
```


### Java Target

First compile a query to Java, for instance:

```
$ bin/qcert -source oql -target java -schema tests/oql/persons.schema tests/oql/persons1.oql
```

To run the resulting Java code, you must first compile it by calling `javac` for the produced Java code, then call `java` with the `RunJava` query runner. You will need to pass it two pieces of information: (i) the location of the Q\*cert runtime for Java, as part of the classpath, and (ii) some input data on which to run the query. From the command line, you can do it as follows, first to compile the Java code:

```
$ javac -cp runtimes/java/bin:bin/lib/* tests/oql/persons1.java
```

Then to run the compiled `persons1` Class:

```
$ java -cp runtimes/java/bin:bin/*:bin/lib/*:tests/oql testing.runners.RunJava \
       -input tests/oql/persons.input \
       persons1
[{"$class":["Customer"],"$data":{"name":"John Doe","age":{"$nat":32},"cid":{"$nat":123}}},
 {"$class":["Customer"],"$data":{"name":"Jane Doe","age":{"$nat":32},"cid":{"$nat":124}}},
 {"$class":["Customer"],"$data":{"name":"Jill Does","age":{"$nat":32},"cid":{"$nat":126}}}]
```


### Spark RDDs Target

TO BE WRITTEN


### Spark DataFrames Target

We provide a Spark example in `tests/spark2`. To compile and run it, do:

```
$ make spark2-runtime
$ cd tests/spark2/
$ run.sh
```


### WASM Target

TO BE WRITTEN


## Caveats

- There is no official support for Windows, although some success has been reported using Cygwin
- The Spark 2 target is still under development
- Some of the source languages are only partially supported
- Only part of the compilation pipeline has been mechanically verified for correctness


## License

Q\*cert is distributed under the terms of the Apache 2.0 License, see
[LICENSE](LICENSE)

## Contributions

Q\*cert is still at an early phase of development and we welcome
contributions. Contributors are expected to submit a 'Developer's
Certificate of Origin' which can be found in [DCO1.1.txt](DCO1.1.txt).

