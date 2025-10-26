Test suite
==========

Building the library
####################

You can test the building of the entire library by running the following command from the top-level directory of the library:
```bash
cabal run GenerateEverything -- --include-deprecated
agda -Werror +RTS -M5G -H3.5G -A128M -RTS -i. -isrc -idoc -WnoUserWarning Everything.agda
```

Golden tests
############

Setup
-----

The golden tests need the `clock` package from Cabal to run.
This can be installed via:
```bash
cabal v1-install --ghc-options='-O1 +RTS -M6G -RTS' clock
```

Running
-------

The golden tests can be run from the top-level directory of the library with the command:
```bash
make testsuite INTERACTIVE='' AGDA_EXEC='~/.cabal/bin/agda'
```
This should take about 5 minutes to run.