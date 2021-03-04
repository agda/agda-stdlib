#!/bin/sh

### You can call this script like so to generate a dependency graph
### of the `Data.List.Base` module:
### ./graph.sh src/Data/List/Base.agda

### Allow users to pick the agda executable they want by prefixing
### the call with `AGDA=agda-X.Y.Z` and default to agda in case
### nothing was picked
AGDA=${AGDA:-"agda"}

### Grab the directory and name of the target agda file
DIR=$(dirname $1)
BASE=$(basename $1 ".agda")
FILE=_build/${DIR}/${BASE}

### Prepare the directory for the dot & tmp files
mkdir -p _build/$DIR

### Generate the dot file for the target agda file
${AGDA} -i. -isrc/ --dependency-graph=${FILE}.dot $1

### Trim the graph to remove transitive dependencies. Without that the
### graphs get too big too quickly and are impossible to render
tred ${FILE}.dot > ${FILE}2.dot
mv ${FILE}2.dot ${FILE}.dot

### Generate an svg representation of the graph
dot -Tsvg ${FILE}.dot > ${FILE}.svg

### Add a symlink to it in the base directory
ln -is ${FILE}.svg ${BASE}.svg
