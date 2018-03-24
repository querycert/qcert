#!/bin/bash
set -euo pipefail

mkdir -p test01_nnrc/src/main/scala/
mkdir -p test01_nnrc/irs/
../../bin/qcert -emit-all -dir test01_nnrc/irs -log-optims-dnrc names -schema test01.schema -source camp -target spark_df -dir-target test01_nnrc/src/main/scala test01.camp
pushd test01_nnrc
sbt assembly
spark-submit --class test01 target/scala-2.11/test01_nnrc-assembly-0.1-SNAPSHOT.jar ../test01.sio
popd

mkdir -p test01_nnrcmr/src/main/scala/
mkdir -p test01_nnrcmr/irs/
../../bin/qcert -emit-all -dir test01_nnrcmr/irs -log-optims-dnrc names -schema test01.schema -path nnrcmr -source camp -target spark_df -dir-target test01_nnrcmr/src/main/scala test01.camp
pushd test01_nnrcmr
sbt assembly
spark-submit --class test01 target/scala-2.11/test01_nnrcmr-assembly-0.1-SNAPSHOT.jar ../test01.sio
popd
