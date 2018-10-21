The Agda standard library
=========================

The standard library aims to contain all the tools needed to easily
write both programs and proofs. While we always try and write efficient
code, we prioritise ease of proof over type-checking and normalisation
performance. If computational performance is important to you, then
perhaps try [agda-prelude](https://github.com/UlfNorell/agda-prelude)
instead. You can browse the library source code in glorious clickable
html [here](https://agda.github.io/agda-stdlib/README.html).

## Quick installation instructions

Use version v0.17 of the standard library with Agda 2.5.4.1.

Install it as follows. Say you are in directory `$HERE` (replace appropriately).
```
  git clone https://github.com/agda/agda-stdlib.git
  cd agda-stdlib
  git checkout v0.17
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

## Contributing to the library

If you would like to suggest improvements, feel free to use the `Issues` tab.
If you would like to make improvements yourself, follow the instructions in
[HACKING](https://github.com/agda/agda-stdlib/blob/master/HACKING.md).

## Non-standard versions of Agda

If you're using an old version of Agda, you can download the corresponding version
of the standard library on the [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary).

If you're using a development version of Agda rather than the latest official release
you should use the `experimental` branch of the standard library rather than `master`.
The `experimental` branch contains non-backwards compatible patches for upcoming
changes to the language.

## Type-checking with the `--safe` flag

After the next full release of Agda, most of the library will be able to
be type-checked with the `--safe` flag. Only the following modules are
not compatible:
```
  Data.Char.Unsafe
  Data.Float.Unsafe
  Data.Nat.Unsafe
  Data.Nat.DivMod.Unsafe
  Data.String.Unsafe
  Data.Word.Unsafe
  IO
  IO.Primitives
  Reflection
  Relation.Binary.PropositionalEquality.TrustMe
```
