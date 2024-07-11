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
In particular, Agda provides core operators such as the ability to declare new data types, functions, pattern-matching and records.
From these operations, it is possible to define all of constructive mathematics and, given suitable postulated axioms, non-constructive mathematics.

While having a minimal set of primitives is desirable in that it decreases the complexity of the implementation of Agda, and therefore increases the trustworthiness of it as an ITP, one immediate consequence is that many things that programmers typically think as basics, (e.g. numbers, strings etc.) have to be first defined.
This makes a standard however means that there is a vast amount of mathematics to rederive, before one can . 

# Design

Designing a standard libary for interactive theorem provers is typically a much bigger challenge than those for standard programming languages.
This is because, not only do they have to provide all the basics of programming (e.g. common data structures, file-system access libraries), they also have to provide a large fraction of basic mathematics.

Organising mathematics is relatively hard. 
The Agda standard library has taken approach somewhere in the middle of the Coq standard library (which is minimal) and that of Lean (which is maximal). 

The focus of the standard library is predominantly on discrete mathematics, which is result of the fact that one of the most popular uses of Agda is as a tool for programming language design and research.


Practical design concerns

* Loading performance, dependency cycles.

* 

# Prominent use cases

The Agda Standard Library has been used in a wide variety of projects, far too many to be exhaustively listed here. A diverse selection, which is in no-way the meant to be an endorsement of these projects above others, are as follows:
- Formalisation of Category Theory [@]
- Verification of Hardware [@]
- Verification of network routing protocols [@]
- ...

# Acknowledgements

We acknowledge the work of the core Agda development team who are not authors on this paper including, but not limited to, 
Andreas Abel, 
Ulf Norell,
Nils Anders Danielsson, 
Andrés Sicard-Ramírez, 
Jesper Cockx and 
Andrea Vezzosi,
without whom Agda itself would not exist.

# References
