# Overview and WARNING

This directory contains the main Q*cert Web page, the Coq
documentation in navigable form, and the Web demos.

This is the official source for the documentation and the external Web
site.

*WARNING: you should never edit the external web site directly*.

Instead: edit the files in this directory, then redeploy to the
external Web site (see below).

# The structure of the documentation

- `demo.html` is the old demo
- `doc.html` contains a starting point for a _Commented Coq Development_ document that helps navigate the code
- `index.html` is the Web site front page
- `demo` is the full SIGMOD'2017 demo
- `figure` is the LaTeX source and makefile for the compilation pipeline
- `html` is the Coq code in navigable form produced by `coq2html`

# To refresh the documentation

If you make changes to the Coq code, you may want to re-generate the
documentation.

You will need a copy of `coq2html` checked out and compiled from the
source. You can find `coq2html` at:
https://github.com/xavierleroy/coq2html. It's written in OCaml and
should compile easily. Once compiled you need to move the produced
`coq2html` executable into your PATH.

Then from the top-level `qcert` direcory, do:

```
make qcert
make documentation
```

This will regenerate the `doc/html` directory

# To update the compilation pipeline

Edit the LaTeX file `doc/figure/compiler-coq.tex`, then do:

```
cd figure
make
```

# To re-deploy the demo and documentation

To deploy the demo and new documentation to the external Q*cert Web
site, first check that the `QUERYCERTDOTIO` in `doc/Makefile` has the
right location for your git checkout of the `querycert.github.io`
project. By default, it's assumed to be checked out from github as a
sibbling of the `qcert` repository.

Then from the `doc` directory, do:
```
make deploy
```

This will copy the main html files, the demos, and Coq documentation.

You can then go to your `querycert.github.io` project and push the
deployed changes to git, which will make the changes visible on the
external Web site.

