The Agda standard library
=========================

The standard library aims to contain all the tools needed to easily
write both programs and proofs. While we always try and write efficient
code, we prioritise ease of proof over type-checking and normalisation
performance. If computational performance is important to you, then
perhaps try [agda-prelude](https://github.com/UlfNorell/agda-prelude)
instead. You can browse the library source code in glorious clickable
html [here](https://agda.github.io/agda-stdlib/README.html).

## Installation instructions

See the instructions [here](https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md)
for how to install version 1.0.1 of the standard library.

## Non-standard versions of Agda

If you're using an old version of Agda, you can download the corresponding version
of the standard library on the [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary).
If you're using a development version of Agda rather than the latest official release
you should use the `experimental` branch of the standard library rather than `master`.
The `experimental` branch contains non-backwards compatible patches for upcoming
changes to the language.

## Type-checking with the `--safe` flag

Most of the library can be type-checked using the `--safe` flag. Please consult
[GenerateEverything.hs](https://github.com/agda/agda-stdlib/blob/master/GenerateEverything.hs#L23)
for a full list of modules that use unsafe features.

## Type-checking with the `--without-k` flag

Most of the library can be type-checked using the `--without-k` flag. Please consult
[GenerateEverything.hs](https://github.com/agda/agda-stdlib/blob/master/GenerateEverything.hs#L74)
for a full list of modules that use axiom K.

## Contributing to the library

If you would like to suggest improvements, feel free to use the `Issues` tab.
If you would like to make improvements yourself, follow the instructions in
[HACKING](https://github.com/agda/agda-stdlib/blob/master/HACKING.md).
