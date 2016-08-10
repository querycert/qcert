Building CACo jars (Experimental)
---------------------------------

It is also possible to build Q*cert as jar file (which can be
useful to embed the compiler). To do so you need a separate OCaml compiler
for Java (http://www.ocamljava.org -- take version 2.0-alpha3).

Make sure to specify an install directory for ocamljava that is
different than your primary OCaml compiler, to avoid conflicts.  Once
ocamljava has been compiled/installed, you need to update the top
level Makefile in the ocaml directory to point the following variable
to the ocamlbuild tool for java. Here is mine, for instance:

## Configuration for the separate ocamljava compiler
OCAMLBUILDJAVA=/Users/simeon/.opam/ocamljava-2.0-alpha3/bin/ocamlbuild

Then you can use the following to build the jars:

make clean ; make jars

Et voila!


