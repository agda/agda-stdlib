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
    affiliation: 3
  - name: McKinna, James
    orcid: 0000-0001-6745-2560
    affiliation: 4
  - name: Abel, Andreas
    orcid: 0000-0003-0420-4492
    affiliation: 2
  - name: van Doorn, Nathan
    orcid: 0009-0009-0598-3663
    affiliation: 5
  - name: Wood, James
    orcid: 0000-0002-8080-3350
    affiliation: 6
  - name: Norell, Ulf
    orcid: 0000-0003-2999-0637
    affiliation: 2
  - name: Kidney, Donnacha Oisín
    orcid: 0000-0003-4952-7359
    affiliation: 7
  - name: Meshveliani, Sergei
    orcid: 0000-0002-4224-6178
    affiliation: 8
  - name: Carette, Jacques
    orcid: 0000-0001-8993-9804
    affiliation: 9
  - name: Rice, Alex
    orcid: 0000-0002-2698-5122
    affiliation: 10
  - name: Hu, Jason Z. S.
    orcid: 0000-0001-6710-6262
    affiliation: 11
  - name: Xia, Li-yiao
    orcid: 0000-0003-2673-4400
    affiliation: 12
  - name: You, Shu-Hung
    affiliation: 12
  - name: Mullanix, Reed
    orcid: 0000-0002-7970-4961
    affiliation: 9
  - name: Kokke, Wen
    orcid: 0000-0002-1662-0381
    affiliation: 10
affiliations:
 - name: University of Western Australia, Australia
   index: 1
 - name: University of Gothenburg and Chalmers University of Technology, Sweden
   index: 2
 - name: University of Strathclyde, United Kingdom
   index: 3
 - name: Heriot-Watt University, United Kingdom
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

Agda [@agda2024manual] is a dependently-typed functional
language that serves both as a traditional programming language
and as an interactive theorem prover (ITP).
In other words, its type system is expressive enough to formulate
complex formal requirements as types, and its compiler allows users to interactively build terms and check that they satisfy these requirements.
Through the Curry-Howard lens [@DBLP:journals/cacm/Wadler15],
these types and terms can be seen respectively as theorem
statements and proofs.

This paper presents the Agda standard library [@agda-stdlib-v2.0], hereafter referred to as `agda-stdlib`, which provides definitions intended to be helpful for users to develop Agda programs and proofs.
Unlike the standard libraries of traditional programming languages, `agda-stdlib` provides not only standard utilities and data structures, but also a range of basic discrete mathematics useful for proving the correctness of programs.

# Statement of need

Most programming languages include a "standard" library offering a basic set of algorithms, data structures, and operating system procedures.
However, there are two reasons why a standard library is particularly significant for Agda compared to traditional programming languages.

First, like other theorem provers, the Agda language provides only a small set of primitives from which programs can be constructed.
As a result, many concepts traditionally considered part of a language must be defined within the program itself.
This approach reduces compiler complexity and enhances its reliability, and also demonstrates the strength of the core Agda language as it can push these concepts out to the library.
For example, in a fresh Agda environment, there is no predefined notion of an integer, let alone more complex data structures such as vectors or maps.
This lack of basic data types increases the need for a standard library when compared to more mainstream languages.

Second, Agda users often seek to prove that programs constructed using data types in the standard library are "correct."
Constructing the proof that a function obeys a specification (e.g. that a sorting function outputs a permutation of the original list in non-decreasing order) often requires more effort, both in terms of lines of code and in developer time, than writing the original operation.
By providing proofs of correctness for operations it defines, the standard library saves users significant time during proof development.

# Impact

A wide range of projects make use of `agda-stdlib`.
In the list below we present a selection of such projects:

- Programming Language Foundations in Agda [@plfa22.08]

- Formalisation of category theory [@hu2021categories]

- Intrinsically typed interpreters for imperative languages [@bach2017intrinsically] and formalisation of type-level computation and subtyping in Scala [@stucki2021theory]

- Formally verified calculus for the synchronous, reactive programming language Esterel [@florence2019esterel]

- Verification of hardware circuit design [@pizani2018pi]

- Verification of routing protocols [@daggitt2023routing]

The library has also been used as a test bed for the design of co-inductive data types in Agda itself, as evidenced by the three different notions of co-inductive data present in the library.
On occasion, the development of `agda-stdlib` has also had a synergistic relationship with that of Agda itself, prompting the implementation of several new language features, which we now discuss.
Firstly, Agda is a research compiler supporting a wide range of possibly incompatible language extensions via command line options.
Examples include `--cubical` (changing the underlying type theory to cubical type theory [@DBLP:journals/jfp/VezzosiMA21]),
`--with-K` (adding support for Streicher's axiom K [@streicher1993investigations], a reasoning principle incompatible with the `--cubical`-enabled type theory),
or `--safe` (an ITP-oriented option enforcing that nothing is postulated and disabling parts of the FFI mechanism).
In order for `agda-stdlib` to be compatible with as many different compiler options as possible, we designed the library to be broken into units
requesting the minimal expressive power needed.
To enable this, in 2019 Agda's language options were categorised as "infective", "coinfective" or "neither".
Once used in a module, an "infective" option will impact all the import*ing* modules; these are typically for theory-changing options such as `--with-K`.
On the contrary, "coinfective" options affect the import*ed* modules; these are typically for options adding extra safety checks like `--safe`.
This categorisation enables libraries to integrate safe Agda code with code that uses "unsafe" operating system calls, while maintaining the safety guarantees of the former.
Another feature motivated by the development of `agda-stdlib` is the ability to attach custom messages to definitions, which are then displayed by the compiler when the definitions are used.
This allowed for the implementation of deprecation warnings, making it easier for users to evolve their code alongside new versions of `agda-stdlib`.

# Design

Designing a standard library for an ITP such as Agda presents several challenges.

Firstly, `agda-stdlib` contains basic discrete mathematics and algebra useful for proving program correctness.
Organising this material into a coherent and logical structure is difficult, although some recent efforts have looked at generating such structure mechanistically [@carette2020leveraging] [@cohen2020hierarchy].
For `agda-stdlib` there is a tension between organising the material to be as general as possible (e.g., defining subtraction using addition and inverse over some abstract algebraic structure) and providing direct and intuitive definitions (e.g., defining subtraction directly over integers).
Additionally, there is the temptation to introduce new representations of existing mathematical objects that are easier to work with for a particular application, which can come at the potential cost of redundancy/duplication.
Some theorem provers such as Rocq [@coq2024manual] have a rich ecosystem of external libraries, which reduces the emphasis on ensuring the existence of canonical definitions for common concepts, at the slightly increased risk of incompatibilities between various libraries.
On the other hand, `batteries` and `mathlib` [@van2020maintaining] for Lean provide a repository of canonical definitions.
Philosophically, `agda-stdlib` is more closely aligned with the approach of the MathLib library, and our aim is to provide canonical definitions for mathematical objects and introduce new representations only sparingly.

A second challenge is that `agda-stdlib` has embraced the "intrinsic style" of dependent types, in which correctness-related invariants are part of data structures, rather than separate predicates.
Many definitions in agda-stdlib use this intrinsic style.
For instance, the final definition of rational numbers is a record type that alongside the numerator and denominator contains a proof showing that the numerator and denominator have no common factors.
The intrinsic style also includes returning proofs rather than, say, booleans from decision procedures.
The standard library for instance uses this approach for its implementation of regular expression matching which along with the match returns a proof justifying it.
Learning how to design a large library that uses this style is an ongoing journey, and we believe that `agda-stdlib` has been one of the first standard libraries to tackle this challenge.

Another significant influence on the design of `agda-stdlib` is Agda’s module system [@ivardeBruin2023] which supports lists of parameters whose types are dependent on the value of parameters earlier in the list.
Several functional languages, such as Haskell [@haskell2010], and ITP libraries, like Lean's MathLib, use type classes as the primary mechanism for ad-hoc polymorphism and overloaded syntax.
While Agda supports an alternative to type-classes known as instance arguments [@devriese2011bright] [@agda2024manual], we have found that the use of qualified, parameterised modules can reproduce most of the abstraction capabilities of instances and type-classes.
The benefits of using parameterised modules instead of type-classes is that it allows users to specify in a single location how to instantiate all the uses of the abstract module parameters and reduces the overhead of instance search at type-checking time.
A drawback is that users may sometimes need to use qualified imports or other similar mechanisms when instantiating the abstract code twice in the same scope.
Another benefit of parameterised modules in the design of `agda-stdlib`, is that they have facilitated the safe and scalable embedding of non-constructive mathematics into what is primarily a constructive library.
Non-constructive operations, such as classical reasoning, can be made available by passing the operations as parameters to the current module, allowing code access to them throughout the module.
This enables users to write non-constructive code, without either having to postulate axioms incompatible with the `--safe` flag, or explicitly pass them through as arguments to every function in the module.

# Testing

Many of the core operations in `agda-stdlib` are accompanied by correctness proofs, and consequently the need for test suites that verify functional correctness is reduced.
However there are tests for two critical areas.
Firstly, it is possible to write code in Agda that cannot be reasoned about directly within Agda itself, e.g. functions that use the foreign function interface and tactics that use Agda macros. Therefore, tests for such code are included in the library's test suite.
Secondly, performance of type-checking and compiled code cannot be analysed inside Agda itself, and so the library includes tests that can be used to reveal regressions in performance.
Having said this, the test suite's coverage in these two areas is not complete as this has not yet been a major priority for the community.

# Notable improvements in version 2.0

Finally, we will briefly discuss the state of `agda-stdlib` version 2.0 [@agda-stdlib-v2.0] for which HTML-annotated sources are available at \url{https://agda.github.io/agda-stdlib/v2.0/}.
The current developers believe we have successfully addressed some of the design flaws and missing functionality present in versions 1.0, including:

- Minimised Dependency Graphs: We have reduced the depth of dependency graphs within the library, ensuring that the most commonly used modules rely on fewer parts of the library. This change has resulted in faster load and compilation times in general.

- Standardisation: We have standardised the construction of mathematical objects such as groups, rings, orders, equivalences, etc., from their sub-objects, enhancing consistency and usability. We have also worked on standardizing morphisms of such objects.

- Tactics Library: We have introduced a growing collection of tactics. Experiments suggest that these tactics are currently slower than those in comparable systems, indicating a potential area for future improvements.

- Testing Framework: We have introduced a golden testing framework that allows users to write their own test suites to assess the performance and correctness of their Agda code.

# Acknowledgements

We would like to thank those members of the Agda development team who are not authors on this paper, but nonetheless whose work on Agda makes the standard library possible. This includes, but is not limited to
Jesper Cockx,
Andrés Sicard-Ramírez and
Andrea Vezzosi.
We also would like to acknowledge the substantial feedback of Nils Anders Danielsson which led to improvements in the papers' presentation.

The authors of this paper are listed approximately in order of contribution to the library. Manuscript preparation was carried out by Matthew Daggitt, Guillaume Allais, James McKinna, Jacques Carette and Nathan van Doorn. A full list of contributors to `agda-stdlib` may be found in the `LICENCE` in the GitHub source tree.

# Funding and conflicts of interest

The authors of this paper have no conflicts of interest to declare.
Many of the contributions to the library by the authors of this paper were made over a significant period of time and while at other institutions than their current affliation. Some of the contributions have been made while receiving funding for related projects, and a non-exhaustive list of such funding follows:

- Jason Z. S. Hu made his contributions during his funded Master's and PhD study.

# References
