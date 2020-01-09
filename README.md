[![Build Status](https://travis-ci.org/agda/agda-stdlib.svg?branch=master)](https://travis-ci.org/agda/agda-stdlib)

The Agda standard library
=========================

The standard library aims to contain all the tools needed to write both
programs and proofs easily. While we always try and write efficient
code, we prioritize ease of proof over type-checking and normalization
performance. If computational performance is important to you, then
perhaps try [agda-prelude](https://github.com/UlfNorell/agda-prelude)
instead.

## Getting started

If you're looking to find your way around the library, there are several
different ways to get started:

- The library's structure and the associated design choices are described
in the [README.agda](https://github.com/agda/agda-stdlib/tree/master/README.agda).

- The [README folder](https://github.com/agda/agda-stdlib/tree/master/README),
which mirrors the structure of the main library, contains examples of how to
use some of the more common modules. Feel free to [open a new issue](https://github.com/agda/agda-stdlib/issues/new) if there's a particular module you feel could do with
some more documentation.

- You can [browse the library's source code](https://agda.github.io/agda-stdlib/README.html)
in glorious clickable HTML.

- Finally, you can get an overview of the entire library by looking at the
[index](https://agda.github.io/agda-stdlib/), which lists all modules
in the library except the deprecated ones.

## Installation instructions

See the [installation instructions](https://github.com/agda/agda-stdlib/blob/master/notes/installation-guide.md) for the latest version of the standard library.

#### Old versions of Agda

If you're using an old version of Agda, you can download the corresponding version
of the standard library on the [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary).
The module index for older versions of the library is also available. For example,
version 0.17 can be found at https://agda.github.io/agda-stdlib/v0.17/, just
replace in the URL 0.17 with the version that you need.

#### Development version of Agda

If you're using a development version of Agda rather than the latest official release,
you should use the `experimental` branch of the standard library rather than `master`.
The `experimental` branch contains non-backward compatible patches for upcoming
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
Even better, if you would like to make the improvements yourself, we have instructions
in [HACKING](https://github.com/agda/agda-stdlib/blob/master/HACKING.md) to help
you get started. For those who would simply like to help out, issues marked with
the [status:low-hanging-fruit](https://github.com/agda/agda-stdlib/issues?q=is%3Aopen+is%3Aissue+label%3A%22status%3A+low-hanging-fruit%22) tag are a good starting point.
