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

Agda[@norell2009dependently] is a functional, dependently-typed language that doubles as both a traditional programming language and as an interactive theorem prover (ITP).
The Agda standard library provides the necessary basics for users to develop Agda programs and proofs.
Unlike the standard libraries of traditional programming languages, the Agda standard library provides not only standard utilities and data structures, but also a large part of the basic mathematics that is essential for proving the correctness of programs.

# Statement of need

Almost all programming languages have some notion of a ``standard'' library which provides a basic set of algorithms, data structures and OS operations, in order to allow users to more quickly develop more complex programs and libraries.
However, there are two reasons why the Agda standard library is perhaps more essential than a traditional standard library.

Firstly, as with most ITPs, in order to decrease the complexity of the compiler implementation and therefore increases its trustworthiness, the Agda language only provides a minimal set of core primitives from which programs can be constructed. 
Consequently many concepts that are traditionally thought of as part of the programming language, instead have to be defined.
For example, in a fresh Agda environment, there is no notion of an integer or a string, let alone advanced data structures such as arrays or maps.

Furthermore, because Agda is a theorem prover, users want to be able to prove that their algorithms they build using these basic data types and data structures are correct. 
Therefore, not only do they need the operations they also need proofs that the corresponding operations such ad addition, concatenation etc. are correctly implemented as well as many of their properties.
Without the Agda standard library, something as simple as defining and proving the correctness of a function that reverses strings would require hundreds of lines of code.

# Impact

The focus of the standard library is predominantly on discrete mathematics, which is result of the fact that one of the most popular uses of Agda is as a tool for programming language design and research.
The library has been used as a basis in a wide variety of projects, far too many to be exhaustively listed here. A diverse selection, which is in no-way the meant to be an endorsement of these projects above others, are as follows:

- Formalisation of Category Theory [@hu2021categories]

- Intrinsically typed [@bach2017intrinsically]

- Calculus for Esterel [@florence2019esterel]

- Verification of hardware [@pizani2018pi]

- Verification of routing protocols [@daggitt2023routing]

As one of the largest Agda developments, the library has also had a synergistic relationship with Agda itself, and has driven the implementation of several features in the language.
For example, thanks to the library Agda now has the ability to add custom compilation messages when using a given definition, and the ability to specify library-wide options in the generic library file that accompanies every library. 
Perhaps the biggest impact, has been the separation of Agda language options into the categories of ''infective'' and ''coinfective'', to allow the library to safely partition code that is natively defined in Agda (and therefore), and code that uses assumptions or operating system calls and therefore cannot be viewed as safe.

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

# Similar libraries

There are many older, and more mature theorem proving systems than Agda, and each with other standard libraries out there. However, they all have some crucial differences.

Isabelle[], Coq[] both have very minimal standard libraries and encourage the use of external libraries developed by the community, and hence there is comparatively less effort on ensuring there are canonical definitions for certain concepts. 
The closest perhaps in this respect to the Agda standard library, is MathLib for Lean which .

Additionally, with the exception of Idris which is a relatively newcomer to the space, other major theorem provers do not lean heavily into dependent-types, use classical axioms and therefore contain many non-constructive results.
Agda is the first library system that uses full-fledged dependent types, and the standard library is the one that uses dependent types seriously. For example, `All`, `Any` predicates, n-ary functions~\cite{}, regular expressions which decide membership. Generic polymorphic n-ary functions[@allais2019generic].

Another interesting key difference from other ITPs is the Agda standard library's relative lack of use of type-classes, a common mechanism for creating interfaces in functional languages and overloading syntax.
It has turned out that the ability to use qualified, parameterised modules as first class objects in Agda, means that type-classes are not as essential as in other languages.
It will be interesting to see if this state of affairs, continues as the library continues to grow and scale.

# Acknowledgements

We would like to thank the core Agda development team who are not authors on this paper, but nonetheless whose work on Agda makes the standrad library possible. This includes, but is not limited to, 
Andreas Abel, 
Ulf Norell,
Nils Anders Danielsson, 
Andrés Sicard-Ramírez, 
Jesper Cockx and 
Andrea Vezzosi,
without whom Agda itself would not exist.

The authors of this paper are listed approximately in order of contribution to the library.

# References
