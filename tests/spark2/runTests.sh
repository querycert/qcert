#!/bin/bash

set -e
set -x

CACO=../../bin/CACo
CADA=../../bin/CADa
TEST=test01

mkdir -p "$TEST"
mkdir -p "$TEST/src/main/scala"
$CACO -io "$PWD/$TEST""_js.io" -dir "$PWD/$TEST/src/main/scala" -target Spark2 "$PWD/$TEST.camp"
$CADA -dir "$PWD/$TEST" "$PWD/$TEST""_js.io"
cp build.sbt.template "$TEST/build.sbt"
cd "$TEST"
sbt "run $TEST""_js.sio"
