---
title: 'The Agda standard library: version 2.0'
tags:
  - Agda
  - Interactive theorem proving
  - Verification
  - Functional programming
authors:
  - name: Daggitt, Matthew L.
    orcid: 0000-0002-2552-3671
    corresponding: true
    affiliation: 1
  - name: Allais, Guillaume
    orcid: 0000-0002-4091-657X
    affiliation: 2
  - name: McKinna, James
    orcid: 0000-0001-6745-2560
    affiliation: 3
  - name: Abel, Andreas
    orcid: 0000-0003-0420-4492
    affiliation: 4
  - name: van Doorn, Nathan
    orcid: 0009-0009-0598-3636
    affiliation: 5
  - name: Wood, James
    orcid: 0000-0002-8080-3350
    affiliation: 6
  - name: Norell, Ulf
    orcid: 0000-0003-2999-0637
    affiliation: 4
  - name: Kidney, Donnacha Oisín
    orcid: 0000-0003-4952-7359
    affiliation: 7
  - name: Meshveliani, Sergei
    orcid: 0000-0002-4224-6178
    affiliation: 8
  - name: Stucki, Sandro
    orcid: 0000-0001-5608-8273
    affiliation: 4
  - name: Carette, Jacques
    orcid: 0000-0001-8993-9804
    affiliation: 9
  - name: Rice, Alex
    orcid: 0000-0002-2698-5122
    affiliation: 10
  - name: Hu, Jason Z. S.
    orcid: 0000-0001-6710-6262
    affiliation: 11
  - name: Xia, Li-yao
    orcid: 0000-0003-2673-4400
    affiliation: 12
  - name: You, Shu-Hung
    orcid: 0009-0003-0003-3945
    affiliation: 13
  - name: Mullanix, Reed
    orcid: 0000-0002-7970-4961
    affiliation: 9
  - name: Kokke, Wen
    orcid: 0000-0002-1662-0381
    affiliation: 10
affiliations:
 - name: University of Western Australia, Australia
   index: 1
 - name: University of Strathclyde, United Kingdom
   index: 2
 - name: Heriot-Watt University, United Kingdom
   index: 3
 - name: University of Gothenburg and Chalmers University of Technology, Sweden
   index: 4
 - name: Independent Software Developer
   index: 5
 - name: Huawei Technologies Research & Development, United Kingdom
   index: 6
 - name: Imperial College London, United Kingdom
   index: 7
 - name: Russian Academy of Sciences, Russia
   index: 8
 - name: McMaster University, Canada
   index: 9
 - name: University of Edinburgh, United Kingdom
   index: 10
 - name: Amazon, USA
   index: 11
 - name: INRIA, France
   index: 12
 - name : Northwestern University, USA
   index: 13
date: 24 September 2024
bibliography: paper.bib
---

# Summary

Agda [@agda2024manual] is a dependently-typed functional language that serves as both a programming language and an interactive theorem prover (ITP).
In Agda, one can formulate requirements on programs as types, and build programs satisfying these requirements interactively.
The Curry-Howard correspondance [@DBLP:journals/cacm/Wadler15] allows types and programs to be seen as theorems and proofs.

We present the Agda standard library [@agda-stdlib-v2.0] (`agda-stdlib`), which provides definitions helpful in the development of programs and proofs.
Unlike standard libraries of traditional programming languages, `agda-stdlib` provides not only standard utilities and data structures, but also basic discrete mathematics useful for proving the correctness of programs.

# Statement of need

Aside from the normal justifications for the existence of standard libraries, there are two reasons why `agda-stdlib` is uniquely needed.

First, Agda as a language is small and does not include concepts usually considered part of a language (such as integers and strings).
This reduces compiler complexity, but means that `agda-stdlib` must define such concepts itself.

Second, as program correctness is important for most Agda users, the functions provided by `agda-stdlib` come with correctness guarantees. Such proofs often require significant effort which should not be offloaded to users.

# Impact

A wide range of projects make use of `agda-stdlib`, including:

- Programming Language Foundations in Agda [@plfa22.08]

- Formalisation of category theory [@hu2021categories]

- Formalisation of aspects of Scala's type system [@stucki2021theory]

- Verification of a calculus for the synchronous, reactive programming language Esterel [@florence2019esterel]

- Verification of hardware circuit design [@pizani2018pi]

- Verification of routing protocols [@daggitt2023routing]

The development of `agda-stdlib` has also had a synergistic relationship with that of Agda itself, helping to both test and motivate new language features.
Firstly, Agda supports a wide range of possibly incompatible language extensions, with examples including `--cubical` (changing the underlying type theory to cubical type theory [@DBLP:journals/jfp/VezzosiMA21]),
`--with-K` (adding support for Streicher's axiom K [@streicher1993investigations]),
or `--safe` (an ITP-oriented option restricting sources of potential unsoundness).
In order for `agda-stdlib` to be compatible with as many different combinations of extensions as possible, it is designed modularly with units
requesting the minimal expressive power needed.
To facilitate this, Agda's extensions were categorised as "infective", "coinfective" or "neither", where
"infective" options impact all the import*ing* modules and "coinfective" options impact the import*ed* modules.
Secondly, another feature motivated by of `agda-stdlib` is attaching custom messages to definitions, displayed on use.
This enabled deprecation warnings, easing the evolution of user code.
The library has also been used as a test bed for different approaches to defining co-inductive data types in Agda itself.

# Design Challenges

Organising libraries of discrete mathematics and algebra coherently is notoriously difficult
[@carette2020leveraging] [@cohen2020hierarchy].
There is a tension between organising the material to be as general as possible and providing direct and intuitive definitions.
Mathematical objects often permit multiple representations with varying application-specific usability profiles -- but this leads to redundancy/duplication.
Some theorem provers ([@coq2024manual], [@paulson1994isabelle]) choose instead to have a rich ecosystem of external libraries, reducing the pressure to have canonical definitions for common concepts at the risk of incompatibilities between libraries.
We have chosen, like Lean's `mathlib` [@van2020maintaining], to provide a repository of canonical definitions.

`agda-stdlib` has embraced the "intrinsic style" of dependent types, in which correctness invariants are part of the data structures themselves.
For instance, the definition of rational numbers carries a proof showing that the numerator and denominator have no common factors.
The intrinsic style also means returning proofs from decision procedures rather than booleans.
We believe that `agda-stdlib` has been one of the first ITP standard libraries to tackle this challenge.

The library has also embraced Agda's parametrised modules to enable polymorphism [@ivardeBruin2023].
This contrasts with other languages which instead rely on type classes for similar functionality.
This lets users specify in a single location how to instantiate all the abstract module parameters and reduces the overhead of instance search.
A drawback is the need for qualified imports when instantiating code twice in the same scope.
Another benefit of parameterised modules is the ability to safely and scalably embed non-constructive mathematics into a primarily constructive library.

# Testing

Correctness proofs do not entirely obviate the need for testing.
There are tests for two critical areas: first, features that cannot be reasoned about internally (such as the FFI and macros); second, performance tests.
However the test suite's coverage is incomplete as this is not a priority for the community.

# Notable improvements in version 2.0

The current developers believe that `agda-stdlib` version 2.0 [@agda-stdlib-v2.0] has successfully addressed some of the
design flaws and missing functionality of previous versions, including:

- Minimised Dependency Graphs: the most commonly used modules rely on fewer parts of the library, resulting in faster load and compilation times in general.

- Standardisation: Mathematical objects such as groups, rings, orders, equivalences, etc., and their morphisms are now uniformly constructed from their sub-objects, enhancing consistency and usability.

- Tactics Library: We have more tactics but experiments suggest that they are currently slower than those in comparable systems.

- Testing Framework: We have introduced a golden testing framework to let users write their own test suites.

HTML-annotated sources for version 2.0 of `agda-stdlib` is available at \url{https://agda.github.io/agda-stdlib/v2.0/}.

# Acknowledgements

Nils Anders Danielsson provided substantial feedback.

The authors of this paper are listed approximately in order of contribution to the library. Manuscript preparation: Daggitt, Allais, McKinna, Carette and van Doorn. A full list of contributors to `agda-stdlib` may be found on GitHub.

# Funding and conflicts of interest

The authors have no conflicts of interest to declare.
The authors made contributions to `agda-stdlib` over a significant period of time, sometimes at other institutions than their current affiliation.
Some contributations were possible thanks to funding for related projects, in particular:

- Jason Z. S. Hu during his funded Master's/PhD.

- Shu-Hung You was supported by the U.S. National Science Foundation (Awards 2237984 and 2421308).

# References
