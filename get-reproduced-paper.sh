#!/bin/bash

# Get the newly generated version of the paper out of the image
id=$(docker create qcert:repro)
docker cp $id:/qcert/sigmod-2017/paper/main.pdf qcert-sigmod-2017-paper-reproduction.pdf
docker rm -v $id
