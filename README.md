The Agda standard library
=========================

The standard library aims to contain all the tools needed to easily
write both programs and proofs. While we always try and write efficient
code, we prioritise ease of proof over type-checking and normalisation
performance. If computational performance is important to you, then
perhaps try [agda-prelude](https://github.com/UlfNorell/agda-prelude)
instead.

## Getting started

If you're looking to find your way around the library, there's various
different ways to get started:

- The library's structure and the associated design choices are described
in the [README.agda](https://github.com/agda/agda-stdlib/tree/master/README.agda).

- The [README folder](https://github.com/agda/agda-stdlib/tree/master/README),
which mirrors the structure of the main library, contains examples of how to
use some of the more common modules. Feel free to open a new
[issue](https://github.com/agda/agda-stdlib/issues/new) if there's a particular
module you feel could do with some more documentation.

- You can browse the library's source code in glorious clickable html
[here](https://agda.github.io/agda-stdlib/README.html).

- Finally you can get an overview of the entire library by looking at the
[index](https://agda.github.io/agda-stdlib/) which lists every module it contains
(minus any deprecated modules).

## Installation instructions

See the instructions [here](https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md)
for how to install version 1.1 of the standard library.

#### Old versions of Agda

If you're using an old version of Agda, you can download the corresponding version
of the standard library on the [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary).

#### Development version of Agda

If you're using a development version of Agda rather than the latest official release
you should use the `experimental` branch of the standard library rather than `master`.
The `experimental` branch contains non-backwards compatible patches for upcoming
changes to the language.

## Type-checking with flags

#### The `--safe` flag

Most of the library can be type-checked using the `--safe` flag. Please consult
[GenerateEverything.hs](https://github.com/agda/agda-stdlib/blob/master/GenerateEverything.hs#L23)
for a full list of modules that use unsafe features.

#### The `--without-k` flag

Most of the library can be type-checked using the `--without-k` flag. Please consult
[GenerateEverything.hs](https://github.com/agda/agda-stdlib/blob/master/GenerateEverything.hs#L74)
for a full list of modules that use axiom K.

## Contributing to the library

If you would like to suggest improvements, feel free to use the `Issues` tab.
Even better if you would like to make the improvements yourself, we have instructions
in [HACKING](https://github.com/agda/agda-stdlib/blob/master/HACKING.md) to help
you get started.
