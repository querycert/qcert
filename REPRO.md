# SIGMOD 2017

This branch is the version of the code that was submitted for SIGMOD 2017, enhanced with scripts to better enable reproduction of the paper.
In particular, it contains a Dockerfile that will install the required dependencies (except one that must be obtained manually, see below), build all the code and tools, reproduce the figures for the paper, and finally, compile and reproduce the submitted paper using the newly computed figures.  The resulting docker image may also be entered and used as a playground to explore the compiler.

# Reproducing

## Setting up dependencies

### Get the code

This can either be obtained by cloning the repository using git (`git clone https://github.com/querycert/qcert.git`), or by downloading it as a [zip file (here)](https://github.com/querycert/qcert/archive/sigmod-repro.zip) and unzipping it.

### TPC-H Benchmarks

The licensing for the TPC-H benchmarks that we use for evaluation does not allow redistribution as part of this artifact, so it must be obtained separately.

Go to the [TPC-H download page (here)](http://www.tpc.org/tpc_documents_current_versions/current_specifications.asp), and click `Download TPC-H_Tools_v2.17.2.zip` under Source Code/TPC-H.  Fill out the form and agree to the license.  You will then receive an email with a link to a individualized page hosting the TPC-H benchmarks.  Download the benchmarks (you will only be able to download them once; if you need to do this again, you must fill out the license form again).  Please accept the suggested filename (which will look something like `...-tpc-h-tool.zip`, where the leading part is some individualized string), and save it to the `qcert` directory (the top level directory of the code).

### Docker

In order to automatically fetch the dependencies and build the code, you will need to install [Docker](https://www.docker.com/) for your platform, and make sure the docker daemon is running.

## Reproduce the paper

you can run the `qcert/reproduce-paper.sh` script.  This will
This will create a new docker image (virtual machine, the image is called `qcert:repro`) with all required dependencies, and use it to build the code, run the experiments, and rebuild the submitted paper.
It will then copy the rebuilt paper out of the image and put it as `qcert/qcert-sigmod-2017-paper-reproduction.pdf`.
Note that the version of the paper published in sigmod 2017 was `qcert-sigmod-2017-paper-original.pdf` is provided 

## Explore

After building the docker image (using, for example, the `qcert/reproduce-paper.sh` script),

Running 
```
docker run -i -t qcert:repro bash
```

will provide a bash shell running in the docker image which can be used to poke around and run the compiler against other examples, including new examples.
`nano` is provided for basic editing needs (and `sudo apt-get` can be used to install other editors as desired).
