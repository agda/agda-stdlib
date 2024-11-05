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
    affiliation: 4
  - name: Abel, Andreas
    orcid: 0000-0003-0420-4492
    affiliation: 11
  - name: van Doorn, Nathan
    orcid: 0009-0009-0598-3663
    affiliation: 5
  - name: Wood, James
    orcid: 0000-0002-8080-3350
    affiliation: 13
  - name: Norell, Ulf
    orcid: 0000-0003-2999-0637
    affiliation: 11
  - name: Kidney, Donnacha Oisín
    orcid: 0000-0003-4952-7359
    affiliation: 9
  - name: Meshveliani, Sergei
    orcid: 0000-0002-4224-6178
    affiliation: 10
  - name: Carette, Jacques
    orcid: 0000-0001-8993-9804
    affiliation: 3
  - name: Rice, Alex
    orcid: 0000-0002-2698-5122
    affiliation: 7
  - name: Hu, Jason Z. S.
    orcid: 0000-0001-6710-6262
    affiliation: 6
  - name: Xia, Li-yiao
    orcid: 0000-0003-2673-4400
    affiliation: 8
  - name: You, Shu-Hung
    affliation: 12
  - name: Mullanix, Reed
    orcid: 0000-0002-7970-4961
    affiliation: 3
  - name: Kokke, Wen
    orcid: 0000-0002-1662-0381
    affiliation: 7
  - name: Others to come
    affiliation: 100
affiliations:
 - name: University of Western Australia, Australia
   index: 1
 - name: University of Strathclyde, United Kingdom
   index: 2
 - name: McMaster University, Canada
   index: 3
 - name: Heriot-Watt University, United Kingdom
   index: 4
 - name: Independent Software Developer
   index: 5
 - name: McGill University, Canada
   index: 6
 - name: University of Edinburgh, United Kingdom
   index: 7
 - name: INRIA, France
   index: 8
 - name: Imperial College London, United Kingdom
   index: 9
 - name: Russian Academy of Sciences, Russia
   index: 10
 - name: University of Gothenburg, Sweden
   index: 11
 - name : Northwestern University, USA
   index: 12
 - name : Huawei Technologies Research & Development, United Kingdom
   index: 13
 - name: UNKNOWN
   index: 100
date: 24 September 2024
bibliography: paper.bib
---

# Summary

Agda [@agda2024manual] is a dependently-typed functional
language that serves both as a traditional programming language
and as an interactive theorem prover (ITP).
In other words, its type system is expressive enough to formulate
complex formal requirements, and its compiler lets users interactively
build programs guaranteed to meet these specifications.
Through the Curry-Howard lens [@DBLP:journals/cacm/Wadler15],
these types and programs can be seen respectively as theorem
statements and proofs.

This paper presents the Agda standard library (hereafter: `agda-stdlib` [@agda-stdlib-v2.0]), which offers fundamental definitions and results necessary for users to quickly begin developing Agda programs and proofs.
Unlike the standard libraries of traditional programming languages, `agda-stdlib` provides not only standard utilities and data structures, but also a substantial portion of the basic discrete mathematics essential for proving the correctness of programs.

# Statement of need

Most programming languages include a "standard" library offering a basic set of algorithms, data structures, and operating system procedures.
However, there are two reasons why a standard library is more important for Agda compared to traditional programming languages.

First, like other theorem provers, the Agda language provides only a small set of primitives from which programs can be constructed.
As a result, many concepts traditionally considered part of a language must be defined within the program itself.
This approach reduces compiler complexity and enhances its reliability, and also shows the strength of the core language
itself as it can indeed push these concepts out to the library.
For example, in a fresh Agda environment, there is no predefined notion of an integer, let alone more complex data structures such as vectors or maps. 
This increases the need for a standard library when compared to more main stream languages.

Second, Agda users often seek to prove that programs constructed using data types from the standard library are "correct."
Therefore, the standard library provides not only operations for these data types but also proofs of their basic properties (e.g., that integer addition is commutative or list concatenation is associative). 
Starting from just the Agda language, something as simple as defining a function to sort a list and proving that it preserves the length of its input would require hundreds of lines of code.

# Impact

A wide range of projects make use of `agda-stdlib`.
A diverse selection, not intended as endorsements over any others, includes:

- Programming Language Foundations in Agda [@plfa22.08]

- Formalisation of category theory [@hu2021categories]

- Intrinsically typed interpreters for imperative languages [@bach2017intrinsically] and formalisation of type-level computation and subtyping in Scala [@stucki2021theory].

- Formally verified calculus for the synchronous, reactive programming language Esterel [@florence2019esterel]

- Verification of hardware circuit design [@pizani2018pi]

- Verification of routing protocols [@daggitt2023routing]

The development of `agda-stdlib` has also had a synergistic relationship with that of Agda itself, prompting the implementation of several new language features.
We discuss two examples below.

First, Agda is a research compiler supporting a wide range of not necessarily inter-compatible language extensions via command line options.
Examples include `--cubical` (changing the underlying type theory to cubical type theory [@DBLP:journals/jfp/VezzosiMA21]),
`--with-K` (adding support for Streicher's axiom K [@streicher1993investigations], a reasoning principle incompatible with the `--cubical`-enabled type theory),
or `--safe` (an ITP-oriented option enforcing that nothing is postulated and consequently disabling the FFI mechanism).
In order for `agda-stdlib` to be compatible with as many different compiler options as possible, we designed the library to be broken into units
requesting the minimal expressive power needed.
To enable this, in 2019 Agda allowed language options to be categorised into "infective", "coinfective" and "neither".
Once used in a module, an "infective" option will impact all the import*ing* modules; these are typically for theory-changing options like `--cubical` or `--with-K`.
On the contrary, "coinfective" options affect the import*ed* modules; these are typically for options adding extra safety checks like `--safe`.
This categorisation enables libraries to integrate safe Agda code with code that uses unsafe operating system calls, while maintaining the safety guarantees of the former.

Second, the development of `agda-stdlib` motivated adding the ability to attach custom messages to definitions, which are then displayed by the compiler when the definitions are used. This enabled the implementation of deprecation warnings amongst other features, and lets end-users more easily evolve their code alongside new versions of `agda-stdlib`.
Thirdly, `agda-stdlib` has been used as a test bed for the design of co-inductive data types, as evidenced by the three different otions of co-inductive data present in the library.

# Design

Designing a standard library for an ITP such as Agda presents several challenges.

Firstly, as discussed, `agda-stdlib` contains much of the basic mathematics useful for proving program correctness.
While the focus on discrete mathematics and algebra reflects the bias in its user base towards programming language theory, organising this material into a coherent and logical structure is difficult, though some recent efforts exist in this direction [@carette2020leveraging,@cohen2020hierarchy].
There is constant tension between being as general as possible (e.g., defining operations over general algebraic structures) and providing clear, straightforward, and intuitive definitions (e.g., defining operations concretely over integers).
Additionally, there is a persistent temptation to introduce new representations of existing mathematical objects that are easier to work with for a particular application, which comes at the cost of duplicating the theory for the new representation.
Theorem provers like Isabelle [@paulson1994isabelle] and Coq [@coq2024manual] have very minimal standard libraries and encouraging the use of external libraries developed by the community, which reduces the emphasis on ensuring the existence of canonical definitions for certain concepts, at the cost of lack of interoperability between various packages.
On the other hand, like `agda-stdlib`, MathLib [@van2020maintaining] for Lean provides a repository of canonical definitions.
Philisophically, `agda-stdlib` is more closely aligned with the approach of the MathLib community, and aims to provide canonical definitions for mathematical objects and introduce new representations only sparingly.

A second challenge is that Agda was the first major ITP to fully embrace dependently-typed programming as the default.
With the exception of Idris, a more recent entrant to the field [@brady2013idris], either other major theorem provers do not support dependent types or their communities and libraries encourage their use only sparingly.
In contrast, nearly everything in `agda-stdlib` makes use of dependent types, with correctness-related invariants being closely integrated with definitions.
For example, we can specify that `reverse` defined on length-indexed vectors is length-preserving *by virtue of its type*.
Furthermore, most proofs consist of evidence-bearing terms for the relevant types and therefore can themselves be computed on.
By using dependent types, the library provides sophisticated features like polymorphic n-ary functions [@allais2019generic] and regular expressions which provide proof of membership when compiled and applied.
While widespread use of dependent types provides powerful tools for users, learning how to design a large, dependently-typed library is an ongoing journey, and we believe the Agda standard library has been one of the first such standard libraries to tackle the challenge.

Unlike other ITPs, Agda’s module system [@ivardeBruin2023] supports module parameters whose type is dependent on earlier module parameters and this has also significantly influenced the design of `agda-stdlib`.
Many functional languages, such as Haskell [@haskell2010], and ITP libraries, like Lean's MathLib, use type classes as the primary mechanism for creating interfaces and overloading syntax. 
While Agda supports a more general form of type-classes via instances [@devriese2011bright], we have found that the use of qualified, dependently-parameterised modules can reproduce most of the abstraction capabilities of type-classes.
The main benefits are that it allows users to explicitly describe which objects are being used to instantiate the abstract code and reduces the risk of time-consuming searches at type-checking time. 
The main drawback is that users needs to use qualified imports when instantiating the abstract code twice in the same scope.
Another benefit of parameterised modules is we have found that they facilitate the safe and scalable embedding of non-constructive mathematics into a largely constructive standard library.
In particular, non-constructive operations, such as classical reasoning, can be made available by passing them as module parameters, allowing code access to them throughout the module.
This enables users to write non-constructive code, without either having to postulate the axioms (which would incompatible with the `--safe` flag), or explicitly pass them through as arguments to every function in the module.

# Testing

In ITPs correctness proofs are regarded as an integral part of creating a collection of operations.
One of the advantages of this is that there is far less need for test suites that verify functional correctness.
However the library’s tests do cover two critical areas.
First is the foreign function interface with the underlying operating system (e.g., reading from the command line, file access, timers) or with Agda itself (e.g. tactics).
Correctness of bindings to an external library or the underlying OS primitives cannot be reasoned about in Agda itself, these operations are tested externally, i.e. in a test suite.
The second area is performance.
Performance of type-checking and compiled code cannot be analysed inside Agda itself, making it necessary for the library include performance tests.
This part of the test suite is sparser, as this has not yet been a major priority for the community.

# Notable achievements in version 2.0

We outline the state of `agda-stdlib` version 2.0 [@agda-stdlib-v2.0] (with HTML-annotated sources at: \url{https://agda.github.io/agda-stdlib/v2.0/}), in which we believe we have successfully addressed some of the design flaws and missing functionality present in versions 1.0-1.7. Key improvements include:

- Minimised Dependency Graphs: We have reduced the depth of dependency graphs within the library, ensuring that the most commonly used modules rely on fewer parts of the library. This change has resulted in significantly faster load times for users during interactive development.

- Standardisation: We have standardised the construction of mathematical objects such as groups, rings, orders, equivalences, etc., from their sub-objects, enhancing consistency and usability. We have also worked on standardizing morphisms of such objects.

- Introduction of a Tactics Library: We have introduced a small but growing tactics library. Experiments have shown that these tactics are currently slower than those in comparable systems, indicating a potential area for future improvements in Agda itself.

- Introduction of a Testing Framework: We have also introduced a testing framework that allows users to write their own test suites, providing a structured way to check the performance and correctness of their non-native Agda code.

# Acknowledgements

We would like to thank the core Agda development team who are not authors on this paper, but nonetheless whose work on Agda makes the standard library possible. This includes, but is not limited to,
Nils Anders Danielsson,
Andrés Sicard-Ramírez,
Jesper Cockx and
Andrea Vezzosi,
without whom Agda itself would not exist.

The authors of this paper are listed approximately in order of contribution to the library. A full list of contributors to `agda-stdlib` may be found in the `LICENCE` in the GitHub source tree.

# Funding and conflicts of interest

The authors of this paper have received no funding to work on the library, and have no conflicts of interest.

# References
