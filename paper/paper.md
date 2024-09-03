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
	orcid: 0000-0000-0000-0000
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

Agda[@norell2009dependently] is a dependently-typed functional language that serves both as a traditional programming language and as an interactive theorem prover (ITP).
This paper introduces the Agda standard library, which offers many of the fundamental definitions and results necessary for users to quickly begin developing Agda programs and proofs.
Unlike the standard libraries of traditional programming languages, the Agda standard library not only provides standard utilities and data structures, but also a substantial portion of the basic mathematics essential for proving the correctness of programs.

# Statement of need

Most programming languages include a "standard" library that offers a basic set of algorithms, data structures, and operating system operations.
However, there are two reasons why a standard library is particularly important in Agda compared to traditional programming languages.

First, like other theorem provers, the Agda language provides only a minimal core set of primitives from which programs can be constructed. 
As a result, many concepts traditionally considered part of a language must be defined within the program itself. 
While this approach reduces compiler complexity and enhances its reliability, it also means that users have access to fewer built-in definitions initially. 
For example, in a fresh Agda environment, there is no predefined notion of an integer or a string, let alone more complex data structures such as arrays or maps.

Second, Agda users often seek to prove that programs constructed using data types from the standard library are "correct." Therefore, the standard library must provide not only the operations for these data types but also proofs of their correctness (e.g., proving that integer addition is commutative or that string concatenation is associative).
Without the Agda standard library, something as simple as defining a function to reverse a string and proving that it preserves the length of the string would require hundreds of lines of code.

# Impact

The Agda standard library has been used in a wide range of projects, too numerous to list exhaustively. 
A diverse selection of such projects, not intended as endorsements over any others, includes:

- Formalisation of category theory [@hu2021categories]

- Intrinsically typed interpreters for imperative languages [@bach2017intrinsically]

- Formally verified calculus for the reactive programming language Esterel [@florence2019esterel]

- Verification of hardware circuit design [@pizani2018pi]

- Verification of routing protocols [@daggitt2023routing]

As one of the largest existing Agda libraries, the standard library has had a synergistic relationship with the development of Agda itself, prompting the implementation of several new language features.
For example, the standard library is designed to be compatible with several different compiler options, including `--cubical` and `--safe`. 
To enable this, in 2019 Agda categorised all language options into two categories of ''infective'' and ''coinfective'', allowing the library to precisely partition code that can be used under certain flag combinations.
This categorisation enables the library to integrate safe code natively defined in Agda with code that uses unsafe operating system calls, while maintaining the safety guarantees of the former.
 
Additionally, the library has directly influenced the language by requesting the ability to attach custom messages to definitions, which are then displayed by the compiler when the definitions are used, enabling the implementation of deprecation warnings.

# Design

Designing a standard library for an ITP such as Agda presents several challenges.

Firstly, as discussed, the standard library contains many of the foundational mathematical results used to prove program correctness.
Even though the library currently focuses on discrete mathematics - reflecting the bias in its user base towards programming language theory - organising this material into a coherent and logical structure is extremely challenging[@carette2020leveraging].
There is a constant tension between being as general as possible (e.g., defining operations over general algebraic structures) and providing clear, straightforward, and intuitive definitions (e.g., defining operations concretely over integers).
Additionally, there is a persistent temptation to introduce new representations of existing mathematical objects that are easier to work with for a particular problem, which comes at the cost of duplicating the theory for the new representation.
Theorem provers like Isabelle[@paulson1994isabelle] and Coq[@coq2024manual] approach these problems by having very minimal standard libraries and encouraging the use of external libraries developed by the community, which reduces the emphasis on ensuring the existence of canonical definitions for certain concepts.
On the other hand, MathLib[@van2020maintaining] for Lean aims to provide a repository of canonical definitions.
The design of the Agda standard library leans more towards the Lean approach, with a high bar set for adding alternative formalisations of the same result.

A second challenge is that Agda was the first major ITP to fully embrace dependently-typed programming as the default. 
With the exception of Idris, a more recent entrant to the field [@brady2013idris], other major theorem provers either do not support dependent types or encourage them only to be used sparingly.
In contrast, nearly everything in the Agda standard library makes use of dependent types, with proofs consisting of evidence-bearing terms of the relevant dependent types.
As a result, the library provides relatively sophisticated features like polymorphic n-ary functions[@allais2019generic], regular expressions which provide proof of membership when compiled and applied, and proof-carrying `All` and `Any` predicates for containers [citation?].
While this provides powerful tools for users, learning how to design such a large-scale, dependently-typed library is an on-going journey. 
Relatedly, the standard library has been used as a test bed for the design of the Agda language itself, as evidenced by the library's inclusion of three different notions of co-inductive data types.

Agda’s unique support for dependently-parameterized modules has also significantly influenced the library’s design. 
Although type classes are a common mechanism for creating interfaces and overloading syntax in other functional languages, the Agda standard library has so far found little need to use them extensively.
While Agda supports a very general form of type classes via instance search, the ability to use qualified, parameterized modules as first-class objects appears to reduce their necessity compared to other functional languages.
Additionally, module parameters enable the safe and scalable embedding of non-constructive mathematics into a constructive system. 
Since Agda is entirely constructive, the vast majority of the standard library is also constructive. 
However, the library provides the option to perform non-constructive, classical reasoning, such as the law of excluded middle, by passing the relevant axioms as module parameters.
This allows users to write such code without directly having to postulate the non-constructive axioms, which would prevent them from using the code with the `--safe` compiler flag.

# Testing

One of the advantages of creating a standard library for an ITP is that proving the correctness of the defined operations is an integral part of the library itself. 
As a result, there is no need for test suites to verify functional correctness. 
However, the library’s test suite does address two critical areas.
The first area is the interface with the underlying operating system (e.g., reading from the command line, file access, timers). 
Since the correctness of the underlying OS cannot be reasoned about in Agda itself, these operations are included in the test suite.
The second area is performance. 
The performance of a program cannot be analysed within Agda, making it necessary to include performance tests. 
Although the library currently includes a few performance tests, this is not a major priority for the community, and remains an area in need of further work.

# Notable achievements in version 2.0

This short paper outlines the state of version 2.0 of the Agda standard library, in which we believe we have successfully addressed some of the significant design challenges present in version 1.0. Key improvements include:

- Minimized Dependency Graphs: We have reduced the depth of dependency graphs within the library, ensuring that the most commonly used modules rely on fewer parts of the library. This change has resulted in significantly faster load times for users during interactive development.

- Standardisation of Mathematical Object Construction: We have standardised the construction of mathematical objects such as groups, rings, orders, equivalences, etc., from their sub-objects, enhancing consistency and usability.

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
