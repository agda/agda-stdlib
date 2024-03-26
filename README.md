[![Ubuntu build](https://github.com/agda/agda-stdlib/actions/workflows/ci-ubuntu.yml/badge.svg)](https://github.com/agda/agda-stdlib/actions/workflows/ci-ubuntu.yml)

[![Ubuntu build](https://github.com/agda/agda-stdlib/actions/workflows/ci-ubuntu.yml/badge.svg?branch=experimental)](https://github.com/agda/agda-stdlib/actions/workflows/ci-ubuntu.yml)

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
in the [README.agda](https://github.com/agda/agda-stdlib/tree/master/doc/README.agda).

- The [README folder](https://github.com/agda/agda-stdlib/tree/master/doc/README),
which mirrors the structure of the main library, contains examples of how to
use some of the more common modules. Feel free to [open a new issue](https://github.com/agda/agda-stdlib/issues/new) if there's a particular module you feel could do with
some more documentation.

- You can [browse the library's source code](https://agda.github.io/agda-stdlib/)
in glorious clickable HTML.

## Installation instructions

See the [installation instructions](https://github.com/agda/agda-stdlib/blob/master/doc/installation-guide.md) for the latest version of the standard library.

#### Old versions of Agda

If you're using an old version of Agda, you can download the corresponding version
of the standard library on the [Agda wiki](http://wiki.portal.chalmers.se/agda/pmwiki.php?n=Libraries.StandardLibrary).
The module index for older versions of the library is also available. For example,
version 1.7 can be found at https://agda.github.io/agda-stdlib/v1.7/, just
replace in the URL 1.7 with the version that you need.

#### Development version of Agda

If you're using a development version of Agda rather than the latest official release,
you should use the `experimental` branch of the standard library rather than `master`.
[Instructions for updating the `experimental` branch](https://github.com/agda/agda-stdlib/blob/master/doc/updating-experimental.txt).
The `experimental` branch contains non-backward compatible patches for upcoming
changes to the language.

## Type-checking with flags

#### The `--safe` flag

Most of the library can be type-checked using the `--safe` flag. Please consult
[GenerateEverything.hs](https://github.com/agda/agda-stdlib/blob/master/GenerateEverything.hs#L32-L82)
for a full list of modules that use unsafe features.

#### The `--cubical-compatible` flag

Most of the library can be type-checked using the `--cubical-compatible` flag, which since Agda v2.6.3 supersedes the former `--without-K` flag. Please consult
[GenerateEverything.hs](https://github.com/agda/agda-stdlib/blob/master/GenerateEverything.hs#L91-L111)
for a full list of modules that use axiom K, requiring the `--with-K` flag.

## Contributing to the library

If you would like to suggest improvements, feel free to use the `Issues` tab.
Even better, if you would like to make the improvements yourself, we have instructions
in [HACKING](https://github.com/agda/agda-stdlib/blob/master/HACKING.md) to help
you get started. For those who would simply like to help out, issues marked with
the [low-hanging-fruit](https://github.com/agda/agda-stdlib/issues?q=is%3Aopen+is%3Aissue+label%3Alow-hanging-fruit) tag are a good starting point.
