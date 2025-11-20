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
the [runtests](admin/runtests/Main.agda) program.

## Test dependencies

The external dependencies of the whole test suite are spelt out in the generic
[_config/template.cabal](_config/template.cabal) cabal file

You may need to bump these dependencies when changing
the version of the GHC compiler we build against.

# Updating the test suite

1. Update [_config/version-numbers.sh](_config/version-numbers.sh)
2. Update the shell command listing explicit version numbers in the
   fenced code block at the top of this README
3. Update bounds in [_config/template.cabal](_config/template.cabal)
4. Update [../.github/workflows/ci-ubuntu.yml](../.github/workflows/ci-ubuntu.yml)
   to run the continuous integration with the new GHC and/or Agda versions.
