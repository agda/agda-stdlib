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



# Main entry point to build and run an Agda program
#
# Typically called like `goldenTest "$1" "echo" "hello world"`
#
# INPUTS:
#    $1 is the agda executable (typically "$1" in the ̀ run` file
#       because this info is provided by the test runner
#    $2 the name of the test as a string
#    $3 is OPTIONAL and corresponds to the extra arguments to pass
#       to the executable obtained by compiling the Agda program
#
# LOGGING:
#    logs/agda-build for the trace produced by Agda
#    logs/cabal-build for the trace produced by cabal+ghc
#
# OUTPUT:
#    the output obtained by running the Agda program is stored in
#    the file named `output`. The test runner will then diff it
#    against the expected file.
goldenTest () {

  AGDA=$1
  TEST_NAME="stdlib-test-$2"

  # Taking extra args for the executable?
  if [ -z ${3-} ]; then
    EXTRA_ARGS=""
  else
    EXTRA_ARGS="-- $3"
  fi

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
  $AGDA --library-file=../../_config/libraries --compile-dir=_build -c --ghc-dont-call-ghc Main.agda > logs/agda-build
  cabal build "$TEST_NAME" --with-compiler "$GHC_EXEC" > logs/cabal-build

  # Run the test
  cabal exec -v0 "$TEST_NAME" --with-compiler "$GHC_EXEC" $EXTRA_ARGS < input > output

  # Clean up after ourselves
  if ! "$HAS_INPUT"; then
    rm input
  fi
  rm "$TEST_NAME".cabal
  rm "$TEST_NAME".agda-lib
  rm _build
  rm dist-newstyle
}
