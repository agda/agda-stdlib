#!/bin/sh

# This script is intended to be sourced from test scripts.
#
# It provides a number of default config options corresponding
# to the compiler versions the stdlib is being tested with
#
# Usage: . ../../config.sh

set -eu

# Ugh, paths are relative to the script sourcing this file!
. ../../_config/version-numbers.sh

goldenTest () {

  AGDA=$1
  TEST_NAME=$2

  # Remember whether the script has an input -- ugh
  if [ -f input ]; then
    HAS_INPUT="true"
  else
    touch input
    HAS_INPUT="false"
  fi

  # Specialise template agda-lib & cabal files
  sed "s/TEST_NAME/$TEST_NAME/g" ../../_config/template.agda-lib > "$TEST_NAME".agda-lib
  sed "s/TEST_NAME/$TEST_NAME/g" ../../_config/template.cabal > "$TEST_NAME".cabal

  # Set up clean logs directory
  rm -rf logs/
  mkdir logs

  # Use shared directories to avoid rechecking stdlib modules
  AGDA_BUILD_DIR=../../_config/_build
  CABAL_BUILD_DIR=../../_config/dist-newstyle

  mkdir -p "$AGDA_BUILD_DIR"
  ln -sf "$AGDA_BUILD_DIR" _build
  mkdir -p "$CABAL_BUILD_DIR"
  ln -sf "$CABAL_BUILD_DIR" dist-newstyle

  # Compile the Agda module and build the generated code
  "$AGDA" --library-file=../../_config/libraries --compile-dir=_build -c --ghc-dont-call-ghc Main.agda > logs/agda-build
  cabal build "$TEST_NAME" --with-compiler "$GHC_EXEC" > logs/cabal-build

  # Run the test
  cabal exec -v0 "$TEST_NAME" --with-compiler "$GHC_EXEC" < input > output

  # Clean up after ourselves
  if ! "$HAS_INPUT"; then
    rm input
  fi
  rm "$TEST_NAME".cabal
  rm "$TEST_NAME".agda-lib
  rm _build
  rm dist-newstyle
}
