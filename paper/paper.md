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
In Agda, one can formulate requirements on programs as types and build programs satisfying these requirements interactively.
The Curry-Howard correspondance [@DBLP:journals/cacm/Wadler15] allows types and programs to be seen as theorems and proofs.
We present the Agda standard library [@agda-stdlib-v2.0] (`agda-stdlib`), which provides functions and mathematical concepts helpful in the development of both programs and proofs.

# Statement of need

Besides providing common utilities and data structures, `agda-stdlib` is especially necessary compared to standard libraries for traditional languages for two reasons.

First, Agda is a small, powerful language that omits concepts usually built-in to a language (e.g. numbers, strings).
This reduces compiler complexity, but leaves `agda-stdlib` to define them.

Second, functions in `agda-stdlib` come with correctness proofs - these require substantial work that should not fall to users.

# Impact

A diverse set of verification projects use `agda-stdlib`, including:

- Programming Language Foundations in Agda [@plfa22.08]

- Category theory [@hu2021categories]

- Scala's type system [@stucki2021theory]

- Calculus for the Esterel language [@florence2019esterel]

- Hardware circuit design [@pizani2018pi]

- Routing protocols [@daggitt2023routing]

The library has had a synergistic relationship with Agda itself, both testing and motivating new language features.
For example, since Agda supports many incompatible language extensions, `agda-stdlib` is structured modularly to remain compatible with different combinations of extensions.
Each module requests only the minimal expressive power it needs and to facilitate this Agda now categories extensions as "infective" (affecting all import*ing* modules), "coinfective" (affecting all import*ed* modules) or "neither".
The library has also served as a test bed for alternative approaches to defining co-inductive data types in Agda.

# Design

Organising libraries of discrete mathematics and algebra coherently is notoriously difficult
[@carette2020leveraging; @cohen2020hierarchy].
There is a tension between maximising generality and providing direct, intuitive definitions.
Mathematical objects often admit multiple representations with different benefits, but this leads to redundancy.
Some ITPs ([@coq2024manual; @paulson1994isabelle]) have a rich ecosystem of external libraries, avoiding canonical definitions at the cost of incompatibilities.
We have chosen, like Lean's `mathlib` [@van2020maintaining], to provide a repository of canonical definitions.

`agda-stdlib` adopts the "intrinsic style" of dependent types, where data structures themselves contain correctness invariants.
For examples, rational numbers carry a proof that the numerator and denominator are coprime and decision procedures return proofs rather than booleans.
To our knowledge, `agda-stdlib` is among the first ITP standard libraries to whole-heartedly embrace this style of programming.

In contrast to the type-class mechanisms often used by other functional languages, `agda-stdlib` primarily supports polymorphism [@ivardeBruin2023] via extensive use of parametrised modules.
This allows users specify instantiations of abstract parameters for whole modules in a single location, reducing the need for instance search.
A drawback is imports must be qualified when code is instantiated multiple times in the same scope.
Parameterised modules are also used to safely and scalably embed non-constructive mathematics into a constructive setting.

# Testing

Correctness proofs do not remove the need for testing performance and features that cannot be reasoned about internally (such as the FFI and macros).
However, the test suite's coverage is incomplete as this is not a community priority.

# Version 2.0

Version 2.0 of `agda-stdlib` [@agda-stdlib-v2.0] has attempted to address some of the design flaws and missing functionality of previous versions, including:

- Minimised Dependency Graphs: core modules rely on fewer parts of the library, resulting in faster load times.

- Standardisation: mathematical objects and their morphisms (e.g. groups, rings) are now constructed more uniformly, enhancing consistency and usability.

- Tactics Library: expanded the set of available tactics (although performance can still be improved).

- Testing Framework: introduced a golden testing framework to let users write their own test suites.

# Acknowledgements

Nils Anders Danielsson provided substantial feedback.

Authors are listed approximately in order of contribution. Manuscript by Daggitt, Allais, McKinna, Carette and van Doorn. A list of all contributors is available on GitHub.

# Funding and conflicts of interest

The authors have no conflicts of interest.
Some contributations were enabled by funding for related projects:

- Jason Z. S. Hu: funded Master's/PhD.

- Shu-Hung You: U.S. National Science Foundation Awards 2237984 and 2421308.

# References
