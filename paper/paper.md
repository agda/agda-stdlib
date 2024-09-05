---
title: 'The Agda standard library: version 2.0'
tags:
  - Agda
  - Interactive theorem proving
  - Verification
  - Functional programming
authors:
  - name: Daggitt, Matthew L.
    orcid: 0000-0000-0000-0000
	corresponding: true
    affiliation: 1
  - name: Allais, Guillaume
	orcid: 0000-0000-0000-0000
    affiliation: 2
  - name: Carette, Jacques
	orcid: 0000-0001-8993-9804
    affiliation: 3
  - name: McKinna, James
	orcid: 0000-0001-6745-2560
    affiliation: 4
  - name: van Doorn, Nathan
	orcid: 0000-0000-0000-0000
    affiliation: 5
  - name: Others to come
	orcid: 0000-0000-0000-0000
	affiliation: 6
affiliations:
 - name: University of Western Australia, Australia
   index: 1
 - name: University of Strathclyde, UK
   index: 2
 - name: McMaster University, Canada
   index: 3
 - name: Heriot-Watt University, UK
   index: 4
 - name: TODO
   index: 5
date: 03 September 2024
bibliography: paper.bib
---

# Summary

Agda [@norell2009dependently] is a dependently-typed functional language that serves both as a traditional programming language and as an interactive theorem prover (ITP).
This paper introduces the Agda standard library, which offers many of the fundamental definitions and results necessary for users to quickly begin developing Agda programs and proofs.
Unlike the standard libraries of traditional programming languages, the Agda standard library not only provides standard utilities and data structures, but also a substantial portion of the basic discrete mathematics essential for proving the correctness of programs.

# Statement of need

Most programming languages include a "standard" library offering a basic set of algorithms, data structures, and operating system procedures.
However, there are two reasons why a standard library is particularly important in Agda compared to traditional programming languages.

First, like other theorem provers, the Agda language provides only a minimal core set of primitives from which programs can be constructed.
As a result, many concepts traditionally considered part of a language must be defined within the program itself.
This approach reduces compiler complexity and enhances its reliability, and also shows the strength of the core language
itself as it can indeed push these concepts out to the library.
For example, in a fresh Agda environment, there is no predefined notion of an integer, let alone more complex data structures such as arrays or maps. Thus the crucial need for a standard library.

Second, Agda users often seek to prove that programs constructed using data types from the standard library are "correct." 
Therefore, the standard library needs to provide all the necessary building blocks: not just operations for these data types but also proofs of their basic properties (e.g., that integer addition is commutative or string concatenation is associative). Starting from just the language, something as simple as defining a string-reversing function and proving that it preserves the length of the string would require hundreds of lines of code.

# Impact

The Agda standard library (hereafter: `agda-stdlib`) has been used in a wide range of projects, too numerous to list exhaustively.
A diverse selection of such projects, not intended as endorsements over any others, includes:

- Formalisation of category theory [@hu2021categories]

- Intrinsically typed interpreters for imperative languages [@bach2017intrinsically]

- Formally verified calculus for the reactive programming language Esterel [@florence2019esterel]

- Verification of hardware circuit design [@pizani2018pi]

- Verification of routing protocols [@daggitt2023routing]

The development of `agda-stdlib` has had a synergistic relationship with that of Agda itself, prompting the implementation of several new language features.
For example, `agda-stdlib` is designed to be compatible with several different compiler options, including `--cubical` and `--safe`.
To enable this, in 2019 Agda categorised all language options into two categories of ''infective'' and ''coinfective'', allowing any library to precisely partition code that can be used under certain flag combinations.
This categorisation enables libraries to integrate safe Agda code with code that uses unsafe operating system calls, while maintaining the safety guarantees of the former.

Additionally, the development needs of `agda-stdlib` have directly influenced the language by requesting the ability to attach custom messages to definitions, which are then displayed by the compiler when the definitions are used, enabling the implementation of deprecation warnings. This lets end-users more easily evolve their code along with the evolution of `agda-stdlib`.

# Design

Designing a standard library for an ITP such as Agda presents several challenges.

Firstly, as discussed, `agda-stdlib` contains much of the foundational mathematics used to prove program correctness.
While the focus on discrete mathematics and algebra reflects the bias in its user base towards programming language theory, organising this material into a coherent and logical structure is extremely challenging [@carette2020leveraging].
There is constant tension between being as general as possible (e.g., defining operations over general algebraic structures) and providing clear, straightforward, and intuitive definitions (e.g., defining operations concretely over integers).
Additionally, there is a persistent temptation to introduce new representations of existing mathematical objects that are easier to work with for a particular application, which comes at the cost of duplicating the theory for the new representation.
Theorem provers like Isabelle [@paulson1994isabelle] and Coq [@coq2024manual] approach these problems by having very minimal standard libraries and encouraging the use of external libraries developed by the community, which reduces the emphasis on ensuring the existence of canonical definitions for certain concepts, at the cost of lack of interoperability between variabous packages.
On the other hand, like `agda-stdlib`, MathLib [@van2020maintaining] for Lean aims to provide a repository of canonical definitions. 

A second challenge is that Agda was the first major ITP to fully embrace dependently-typed programming as the default.
With the exception of Idris, a more recent entrant to the field [@brady2013idris], other major theorem provers either do not support dependent types or encourage spare usage.
In contrast, nearly everything in `agda-stdlib` makes use of dependent types, with correctness-related invariants being closely integrated with definitions.
Furthermore most proofs consist of evidence-bearing terms for the relevant types, rather than being "irrelevant".
As a result, the library provides relatively sophisticated features like polymorphic n-ary functions [@allais2019generic], regular expressions which provide proof of membership when compiled and applied, and proof-carrying `All` and `Any` predicates for containers [citation?].
While this provides powerful tools for users, learning how to design such a large-scale, dependently-typed library is an ongoing journey. The Agda standard library is the first such to tackle this challenge.
Relatedly, `agda-stdlib` has been used as a test bed for the design of the Agda language itself, as evidenced by the library's inclusion of three different notions of co-inductive data types.

Agda’s unique support for dependently-parameterized modules has also significantly influenced the library’s design.
Although type classes are a common mechanism for creating interfaces and overloading syntax in other functional languages such as Haskell [@haskell2010], and other ITPs like Coq and Lean's MathLib use them extensively as a core feature of their design, `agda-stdlib` has so far found little need to exploit such an approach.
While Agda supports a very general form of instance search, the ability to use qualified, parameterized modules as first-class objects appears to reduce their necessity compared to the languages mentioned above. 
Additionally, module parameters enable the safe and scalable embedding of non-constructive mathematics into a constructive system.
Since Agda is entirely constructive, the vast majority of `agda-stdlib` is also constructive.
Non-constructive methods, such as classical reasoning, can be achieved by passing the relevant axioms as module parameters.
This enables users to write provably 'safe' non-constructive code, i.e. without having to *postulate* such axioms.

# Testing

One of the advantages of ITPs is that correctness proofs are regarded as an integral part of creating a collection of structures and operations.
Thus there is no need for test suites to verify functional correctness.
However the library’s test suite does address two critical areas.
First is the foreign function interface with the underlying operating system (e.g., reading from the command line, file access, timers).
Correctness of bindings to an external library or the underlying OS' primitives cannot be reasoned about in Agda itself, these operations are tested externally, i.e. in a test suite.
The second area is performance.
Performance also cannot be analysed internally, making it necessary to include performance tests.
This part of the test suite is sparser, as this has not yet been a major priority for the community.

# Notable achievements in version 2.0

We outline the state of version 2.0 of `agda-stdlib`, where we believe we have successfully addressed some of the significant design challenges present in versions 1.0-1.7. Key improvements include:

- Minimized Dependency Graphs: We have reduced the depth of dependency graphs within the library, ensuring that the most commonly used modules rely on fewer parts of the library. This change has resulted in significantly faster load times for users during interactive development.

- Standardisation: We have standardised the construction of mathematical objects such as groups, rings, orders, equivalences, etc., from their sub-objects, enhancing consistency and usability. We have also worked on standardizing morphisms of such objects.

- Introduction of a Tactics Library: We’ve introduced a small but growing tactics library. Experiments have shown that these tactics are currently slower than those in comparable systems, indicating a potential area for future improvements in Agda itself.

- Introduction of a Testing Framework: We have also introduced a testing framework that allows users to write their own test suites, providing a structured way to check the performance and correctness of their non-native Agda code.

# Acknowledgements

We would like to thank the core Agda development team who are not authors on this paper, but nonetheless whose work on Agda makes the standard library possible. This includes, but is not limited to,
Andreas Abel,
Ulf Norell,
Nils Anders Danielsson,
Andrés Sicard-Ramírez,
Jesper Cockx and
Andrea Vezzosi,
without whom Agda itself would not exist.

The authors of this paper are listed approximately in order of contribution to the library.

# References
