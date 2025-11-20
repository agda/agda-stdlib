# Running the test suite

You can run the test suite by going back to the main project directory
and running (change accordingly if you have the right versions of Agda
& GHC installed but the executable names are different).

```shell
AGDA_EXEC=agda-2.6.4 GHC_EXEC=ghc-9.2.8 make testsuite
```


# Structure of the test suite

## Configuration

The Agda & GHC version numbers the stdlib is tested against
are specified in [_config/version-numbers.sh](_config/version-numbers.sh)

## Test runner

The test runner is defined in [admin/runtests/](admin/runtests/).
It is compiled using an ad-hoc [run](admin/runtests/run) file using
the shared configuration and the resulting executable is copied to
the root of the tests directory.

If you want to add new tests, you need to list them in
[runtests.agda](admin/runtests/runtests.agda).

## Test dependencies

The external dependencies of each test are spelt out in:

* either the generic [_config/template.cabal](_config/template.cabal) cabal file
if they don't need any additional dependencies
* or the test-specific cabal file (e.g. [data/appending/appending.cabal](data/appending/appending.cabal)) otherwise

You may need to bump these dependencies when changing
the version of the compiler backend we build against.

# Updating the test suite

1. Update [_config/version-numbers.sh](_config/version-numbers.sh)
2. Update the command listing explicit version numbers at the top of this README
3. Update bounds in [_config/template.cabal](_config/template.cabal)
   as well as all the test-specific cabal files in the X/Y/ subdirectories
4. Update [../.github/workflows/ci-ubuntu.yml](../.github/workflows/ci-ubuntu.yml)
   to run the continuous integration with the new GHC and/or Agda versions.
