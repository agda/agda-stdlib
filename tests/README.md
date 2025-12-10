# Running the test suite

You can run the test suite by going back to the main project directory
and running (change accordingly if you have the right versions of Agda
& GHC installed but the executable names are different).

```shell
AGDA_EXEC=agda-2.6.8 GHC_EXEC=ghc-9.12.2 make testsuite
```

# Structure of the test suite

## Test case

Each test case is under 2 levels of nesting (this is hard-coded)
and should comprise:

1. A `Main.agda` file containing a `main` entrypoint
2. An `expected` file containing the expected output of running `Main`
3. A `run` file describing how to run `Main` (most likely implemented
   using the `goldenTest` function defined in
   [_config/config.sh](_config/config.sh).
4. Optionally, an `input` file for the stdin content to feed to
   the executable obtained by compiling `Main`.

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
