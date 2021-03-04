#!/bin/sh
DIR=$(dirname $1)
BASE=$(basename $1 ".agda")
FILE=_build/${DIR}/${BASE}
mkdir -p _build/$DIR
agda -i. -isrc/ --dependency-graph=${FILE}.dot $1
tred ${FILE}.dot > ${FILE}2.dot
mv ${FILE}2.dot ${FILE}.dot
dot -Tsvg ${FILE}.dot > ${FILE}.svg
ln -is ${FILE}.svg ${BASE}.svg
