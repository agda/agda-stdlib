#!/bin/sh

# This script is intended to be sourced from test scripts.
#
# It provides a number of default config options corresponding
# to the compiler versions the stdlib is being tested with
#
# Usage: . PATH/TO/version-numbers.sh

if [ -z ${AGDA_EXEC} ]; then
    export AGDA_EXEC=agda-2.6.4
fi

if [ -z ${GHC_EXEC} ]; then
  export GHC_EXEC=ghc-9.2.8
fi
