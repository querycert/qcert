#!/bin/bash

BASE_DIR="`dirname $0`"
BASE_DIR=`cd ${BASE_DIR}; pwd`

# Build the image.  This will get all the dependencies, recompile everything, and generate a new version of the paper
docker build -t qcert:repro .

echo "Copying the newly reproduced paper into 'qcert-sigmod-2017-paper-reproduction.pdf'"
${BASE_DIR}/get-reproduced-paper.sh
