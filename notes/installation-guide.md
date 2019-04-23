Installation instructions
=========================

Use version v1.0 of the standard library with Agda 2.6.0.

Install it as follows. Say you are in directory `$HERE` (replace appropriately).
```
  git clone https://github.com/agda/agda-stdlib.git
  cd agda-stdlib
  git checkout v1.0
  cabal install
```
The last comment is optional, omit it if you are lacking [cabal](https://www.haskell.org/cabal/).

Register it by adding the following line to `$HOME/.agda/libraries`:
```
  $HERE/agda-stdlib/standard-library.agda-lib
```

To use the standard library in you project `$PROJECT`, put a file
`$PROJECT.agda-lib` file in the project root containing:
```
  depend: standard-library
  include: $DIRS
```
where `$DIRS` is a list of directories where Agda
searches for modules, for instance `.` (just the project root).

If you want to refer to the standard library in all your
projects, add the following line to `$HOME/.agda/defaults`
```
  standard-library
```

Find the full story at [readthedocs](http://agda.readthedocs.io/en/latest/tools/package-system.html).
