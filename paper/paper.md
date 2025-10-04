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

- Verification of a calculus for the synchronous, reactive Esterel language [@florence2019esterel]

- Verification of hardware circuit design [@pizani2018pi]

- Verification of routing protocols [@daggitt2023routing]

The development of `agda-stdlib` has also had a synergistic relationship with that of Agda itself, helping to both test and motivate new language features.
For example, Agda supports a wide range of incompatible language extensions and `agda-stdlib` is designed modularly in order to be compatible with many different combinations of extensions.
Modules then request the minimal expressive power needed.
To facilitate this, Agda's extensions were categorised as "infective", "coinfective" or "neither", where
"infective" options impact all the import*ing* modules and "coinfective" options impact the import*ed* modules.
The library has also acted as a test bed for different approaches to defining co-inductive data types in Agda.

# Design Challenges

Organising libraries of discrete mathematics and algebra coherently is notoriously difficult
[@carette2020leveraging] [@cohen2020hierarchy].
There is a tension between being as general as possible and providing direct and intuitive definitions.
Mathematical objects often permit multiple representations with different advantages -- but this leads to redundancy/duplication.
Some ITPs ([@coq2024manual], [@paulson1994isabelle]) have a rich ecosystem of external libraries, avoiding canonical definitions at the risk of incompatibilities between libraries.
We have chosen, like Lean's `mathlib` [@van2020maintaining], to provide a repository of canonical definitions.

`agda-stdlib` has embraced the "intrinsic style" of dependent types, where data structures themselves contain correctness invariants.
For instance, rational numbers include a proof that the numerator and denominator have no common factors and decision procedures return proofs rather than booleans.
We believe that `agda-stdlib` has been one of the first ITP standard libraries to tackle this challenge.

The library has also embraced Agda's parametrised modules to facilitate polymorphism [@ivardeBruin2023].
This contrasts with other functional languages which often rely on type classes for similar functionality.
This lets users specify in a single location how to instantiate the abstract parameters in the module and reduces the overhead of instance search.
A drawback is imports must be qualified when instantiating code multiple times in the same scope.
The library also uses parameterised modules to safely and scalably embed non-constructive mathematics into a constructive library.

# Testing

Correctness proofs do not remove the need for testing performance and features that cannot be reasoned about internally (such the FFI and macros).
However, the test suite's coverage is incomplete as this is not a priority for the community.

# Notable improvements in version 2.0

Version 2.0 of `agda-stdlib` [@agda-stdlib-v2.0] has attempted to address some of the design flaws and missing functionality of previous versions, including:

- Minimised Dependency Graphs: core modules rely on fewer parts of the library, resulting in faster load and compilation times in general.

- Standardisation: objects such as groups, rings etc., and their morphisms are now constructed uniformly, enhancing consistency and usability.

- Tactics Library: expanded the list of available tactics, although experiments suggest performance can be improved.

- Testing Framework: introduced a golden testing framework to let users write their own test suites.

HTML-annotated sources for version 2.0 of `agda-stdlib` is available at \url{https://agda.github.io/agda-stdlib/v2.0/}.

# Acknowledgements

Nils Anders Danielsson provided substantial feedback.

Authors are listed approximately in order of contribution to the library. Manuscript by Daggitt, Allais, McKinna, Carette and van Doorn. All contributors to `agda-stdlib` is available on GitHub.

# Funding and conflicts of interest

The authors have no conflicts of interest to declare.
Some contributations were possible thanks to funding for related projects, in particular:

- Jason Z. S. Hu: funded Master's/PhD.

- Shu-Hung You: U.S. National Science Foundation Awards 2237984 and 2421308.

# References
