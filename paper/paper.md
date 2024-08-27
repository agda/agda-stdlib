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
    equal-contrib: true
    affiliation: 1
  - name: Allais, Guillaume
	orcid: 0000-0000-0000-0000
    equal-contrib: true
    affiliation: 2
  - name: Carrete, Jacques
	orcid: 0000-0000-0000-0000
    equal-contrib: true # (This is how you can denote equal contributions between multiple authors)
    affiliation: 3
  - name: McKinna, James
	orcid: 0000-0000-0000-0000
    corresponding: true # (This is how to denote the corresponding author)
    affiliation: 4
affiliations:
 - name: University of Western Australia, Australia
   index: 1
 - name: Institution Name, Country
   index: 2
 - name: Independent Researcher, Country
   index: 3
date: 13 August 2017
bibliography: paper.bib
---

# Summary

Agda[@norell2009dependently] is a functional, dependently-typed programming language that doubles as both a traditional programming language and as an interactive theorem prover (ITP).
The Agda standard library provides the vital building blocks with which users can develop Agda programs.
Unlike the standard libraries of traditional programming languages, as the standard library for an ITP the Agda standard library provides not only standard utilities and data structures, but also a large part of the basic mathematics that is essential for proving the correctness of programs.

# Statement of need

Similar to many ITPs, Agda provides a minimal set of core primitives from which programs can be constructed. 
This is desirableas it decreases the complexity of Agda's implementation, and therefore increases its trustworthiness.
Core primitives include the ability to declare new data types, records and functions and to destruct data using pattern-matching.

However, one immediate consequence of having a minimal set of primitives is that many things that programmers typically think of as the basic building blocks of any programming language have to be defined.
For example, in a fresh Agda environment, there is no notion of an integer or a string, let alone advanced data structures such as lists, maps or similar.
Furthermore, because Agda is a theorem prover, users want to be able to prove that their algorithms built using these basic data types and data structures are correct. Therefore, not only do they need the operations they also need proofs that the corresponding operations such ad addition, concatenation etc. are correctly implemented.
Without the Agda standard library, it would therefore take hundreds of lines of code to do something as simple as prove the correctness of a function for reversing strings.

# Impact

The focus of the standard library is predominantly on discrete mathematics, which is result of the fact that one of the most popular uses of Agda is as a tool for programming language design and research.
The library has been used in a wide variety of projects, far too many to be exhaustively listed here. A diverse selection, which is in no-way the meant to be an endorsement of these projects above others, are as follows:
- Formalisation of Category Theory [@hu2021categories]
- Intrinsically typed [@bach2017intrinsically]
- Calculus for Esterel [@florence2019esterel]
- Verification of hardware [@]
- Verification of protocols [@]

* Impact on Agda itself. For example, deprecation warnings, careful management of options (infective/coinfective, safe, cubical compatible etc.), options in the .agda-lib description file.

# Design

Designing a standard libary for interactive theorem provers, and Agda in particular, is typically a bigger challenge than those for standard programming languages for several reasons:

Firstly, not only does the standard library have to provide all the basics of programming (e.g. data structures, file-system operations), they also have to provide a large fraction of basic mathematics.
Organising mathematics is relatively hard~\cite{} Jacques, cite packing/unpacking of records. 

Secondly, Agda was the first ITP to take dependently-typed programming seriously. 
A lot of learning of how to do dependently-typed design of large-scale formalisation. Still somewhat in a state of flux as we're learning new ways to organise concepts. 

Thirdly, and related to the previous point, the standard library has been used as a test bed for the design of the Agda language itself. For example, the library contains three different notions of co-inductive definitions. 

Practical design concerns

Version 2.0 of the library has ironed out many of the design wrinkles found in earlier versions.
This includes:
- minimising the dependency graphs so that core, commonly used modules depend on far fewer parts of the library, and hence load far faster for the user during interactive development.
- standardisation of how mathematical objects such as groups, rings, orders, equivalences etc. are constructed from their subparts.
- the introduction of tactics 
- tactics - although tend to be slow (Agda)
- testing infrastructure

# Testing

One of the advantages of working in a thereom prover, is that much of the core functionality of the library is __proven__ to be correct, and therefore we do not need correctness tests. 

These leaves two crucial areas that do need to be tested. 
The first is that the standard library provides several modules that provide an interface with the underlying operating system (e.g. reading from the command line, file access, timers).
As the correctness of the underlying OS cannot be reasoned about in Agda itself, these functionalities do have tests.
The second area, is performance. Again, the performance of the Agda compiler cannot be reasoned about in Agda, and therefore . While the library does have a couple of tests, performance is still very much an area that needs work.

# Other similar libraries

Constructive, as opposed to some other libraries. Although, we have classical axioms one can easily introduce as arguments or constructive. 

Isabelle
 - has small standard library (AFP external, free for all)

Coq
 - Coq standard library (which is minimal).

Lean 
 - more similar MathLib (for Lean) (which is maximal)

Idris
 - very limited. Basically on what you need to bootstrap the language.
 
Mention lack of type-classes? Qualified + parameterised module naming.

Agda is the only system that uses full-fledged dependent types, and the standard library is the one that uses dependent types seriously. For example, `All`, `Any` predicates, n-ary functions~\cite{}, regular expressions which decide membership.

The Agda standard library has taken approach somewhere in the middle of the that of . 

# Acknowledgements

We would like to thank the core Agda development team who are not authors on this paper, but nonetheless whose work on Agda makes the standrad library possible. This includes, but is not limited to, 
Andreas Abel, 
Ulf Norell,
Nils Anders Danielsson, 
Andrés Sicard-Ramírez, 
Jesper Cockx and 
Andrea Vezzosi,
without whom Agda itself would not exist.

# References
