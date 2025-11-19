#!/bin/sh

# This script is intended to be sourced from test scripts.
#
# It provides a number of default config options corresponding
# to the compiler versions the stdlib is being tested with
#
# Usage: . PATH/TO/config.sh

set -e

if [ -z ${AGDA_EXEC} ]; then
    export AGDA_EXEC=agda-2.6.4
fi

if [ -z ${GHC_EXEC} ]; then
  export GHC_EXEC=ghc-9.2.8
fi

goldenTest () {

  AGDA=$1
  TEST_NAME=$2

  sed "s/TEST_NAME/$TEST_NAME/g" ../../_config/template.agda-lib > "$TEST_NAME".agda-lib
  sed "s/TEST_NAME/$TEST_NAME/g" ../../_config/template.cabal > "$TEST_NAME".cabal

  # Set up clean logs directory
  rm -rf logs/
  mkdir logs

  # Use pre-existing build directory to avoid rechecking stdlib modules
  ln -sf ../../_build _build

  # Compile the Agda module and build the generated code
  $AGDA --compile-dir=_build -c --ghc-dont-call-ghc Main.agda > logs/agda-build
  cabal build "$TEST_NAME" --with-compiler "$GHC_EXEC" > logs/cabal-build

  # Run the test
  cabal exec -v0 "$TEST_NAME" --with-compiler "$GHC_EXEC" > output

  # Clean up after ourselves
  rm "$TEST_NAME".cabal
  rm -R dist-newstyle
  rm -R _build/MAlonzo/Code/

}
