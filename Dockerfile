# Start with a base container that has opam (ocaml package manager) installed
FROM ocaml/opam:ubuntu

# Document who is responsible for this image
MAINTAINER Avi Shinnar "shinnar@us.ibm.com"

# install the required dependencies that are managed by the system dependency manager
USER root
RUN apt-get update && \
    apt-get install -y \
     ant \
     findutils \
     gcc \
     m4 \
     make \
     openjdk-8-jdk \
     python-matplotlib \
     python-numpy \
     python-pandas \
     texlive \
     texlive-latex-extra \
     texlive-math-extra \
     wget \
     zip && \
    wget https://dl.bintray.com/sbt/debian/sbt-0.13.16.deb && \
    dpkg -i sbt-0.13.16.deb 
USER opam

# install the required dependencies that are managed by opam
RUN opam install coq.8.5.3 ocamlbuild.0.11.0 menhir.20170418 base64.2.1.2 yojson

ENV JAVA_HOME /usr/lib/jvm/java-8-openjdk-amd64

# set /qcert as the base directory that we will install into
WORKDIR /qcert

# copy over the files that we need from the repository
# note that files matching the globs in .dockerignore will not be copied
COPY Makefile /qcert/
COPY bin /qcert/bin
COPY coq /qcert/coq
COPY ocaml /qcert/ocaml
COPY lib /qcert/lib
COPY runtime /qcert/runtime
COPY javaService /qcert/javaService
COPY sqlParser /qcert/sqlParser
COPY samples /qcert/samples
COPY *tpc*tool*.zip /qcert/samples/sql/tpc/linuxOnly/
COPY sigmod-2017 /qcert/sigmod-2017

# COPY sets the permissions of the files so that only root can access them, so we chown them over to our non-root user
RUN sudo chown -R opam /qcert

# compile the tools
RUN make -C javaService && make -C sqlParser && make -C javaService install && make -C samples/sql/tpc/linuxOnly

# compile and extract the qcert compiler and its documentation
RUN eval `opam config env` && make remove_all_derived && make all && make html

# Compile the qcert samples, including the TPC-H queries, and copy those queries over to the benchmark directory
RUN make -C samples && \
    cp /qcert/samples/sql/tpc/q*.sql /qcert/sigmod-2017/bench/

# recompile the various queries, calculate the appropriate statistics, and reproduce the figures used in the paper.
RUN mkdir -p ~/.config/matplotlib/ && \
    echo "backend : Agg" >> ~/.config/matplotlib/matplotlibrc && \
    eval `opam config env` && \
    make -C sigmod-2017/bench

# Recompile the actual paper.  Note that the figures in the paper directory are symlinks to the files produced by the preceeding step.
RUN make -C sigmod-2017/paper clean pdf
