---
title: 'The Agda standard library: version 2.0'
tags:
  - Agda
  - interactive theorem proving
  - verification
  - functional programming
authors:
  - name: Adrian M. Price-Whelan
    orcid: 0000-0000-0000-0000
    equal-contrib: true
    affiliation: "1, 2" # (Multiple affiliations must be quoted)
  - name: Author Without ORCID
    equal-contrib: true # (This is how you can denote equal contributions between multiple authors)
    affiliation: 2
  - name: Author with no affiliation
    corresponding: true # (This is how to denote the corresponding author)
    affiliation: 3
  - given-names: Ludwig
    dropping-particle: van
    surname: Beethoven
    affiliation: 3
affiliations:
 - name: Lyman Spitzer, Jr. Fellow, Princeton University, USA
   index: 1
 - name: Institution Name, Country
   index: 2
 - name: Independent Researcher, Country
   index: 3
date: 13 August 2017
bibliography: paper.bib
---

# Summary

Agda CITE is a programming language used as a platform for cutting-edge
research into programming language technology.
Agda functions both as a traditional programming language and as an interactive
theorem prover, allowing users to  write proofs as well as programs.
The Agda standard library therefore provides a foundation for Agda users to develop proofs and programs.
Unlike standard libraries of traditional programming languages, the Agda standard library must provide not
just standard utility functions and data structures, but also large parts of basic mathematics
that are essential for proving the correctness of programs.

# Motivation

Agda is a functional programming language that doubles as an interactive theorem prover. 
It's purpose is to write.
Agda is 

The essence of a proof assistant is to have as small a set of axioms as possible and derive almost everything else from those axioms. 
Agda is no exception, and provides a small set of primitive operations, including the ability to define new types, pattern-matching and X. 
From this, it is possible to define all of constructive mathematics (and, given suitable postulates, non-constructive mathematics). 

Indeed, things that many programmers would have thought of as basics, (e.g. numbers, strings etc.) have to be derived. This however means that there is vast amount of mathematics to rederive, before one can . 

# Design

Designing a standard libary for interactive theorem provers is typically a much bigger challenge than those for standard programming langauges.
This is because, not only do they have to provide all the basics of programming (e.g. common data structures, file-system access libraries), they also have to provide a large fraction of basic mathematics.

Organising mathematics is relatively hard, as there is a lot of it. 
The Agda standard library has taken approach somewhere in the middle of the Coq standard library (which is minimal) and that of Lean (which is maximal). 

The focus of the standard library is predominantly on discrete mathematics, which is result of the fact that one of the primary uses of Agda is as a tool for programming language design and research.

# Prominent use cases

The Agda Standard Library has been used in a wide variety of projects, far too many to be exhaustively listed here. A diverse selection, which is in no-way the meant to be an endorsement of these projects above others, are as follows:
- Formalisation of Category Theory
- Verification of Hardware
- Verification of network routing protocols 
- ...

# Acknowledgements

We acknowledge the work of the core Agda development team who are not authors
on this paper including, but not limited to, Andreas Abel, Ulf Norell,
Nils Anders Danielsson, Andrés Sicard-Ramírez, Jesper Cockx and Andrea Vezzosi,
without whom Agda itself would not exist.

# References
