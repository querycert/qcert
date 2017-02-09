#!/bin/bash
set -euo pipefail

echo $PATH

mkdir -p test01_nnrc/src/main/scala/
qcert -schema test01.schema -target spark_dataset -dir-target test01_nnrc/src/main/scala test01.camp
pushd test01_nnrc
sbt assembly
spark-submit --class R01 target/scala-2.11/test01_nnrc-assembly-0.1-SNAPSHOT.jar ../test01.sio
popd
