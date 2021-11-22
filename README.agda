{-# OPTIONS --rewriting --guardedness --sized-types #-}

module README where

------------------------------------------------------------------------
-- The Agda standard library, version 1.7.1
--
-- Authors: Nils Anders Danielsson, Matthew Daggitt, Guillaume Allais
-- with contributions from Andreas Abel, Stevan Andjelkovic,
-- Jean-Philippe Bernardy, Peter Berry, Bradley Hardy Joachim Breitner,
-- Samuel Bronson, Daniel Brown, Jacques Carette, James Chapman,
-- Liang-Ting Chen, Dominique Devriese, Dan Doel, Érdi Gergő,
-- Zack Grannan, Helmut Grohne, Simon Foster, Liyang Hu, Jason Hu,
-- Patrik Jansson, Alan Jeffrey, Wen Kokke, Evgeny Kotelnikov,
-- Sergei Meshveliani, Eric Mertens, Darin Morrison, Guilhem Moulin,
-- Shin-Cheng Mu, Ulf Norell, Noriyuki Ohkawa, Nicolas Pouillard,
-- Andrés Sicard-Ramírez, Lex van der Stoep, Sandro Stucki, Milo Turner,
-- Noam Zeilberger and other anonymous contributors.
------------------------------------------------------------------------

-- This version of the library has been tested using Agda 2.6.2.

-- The library comes with a .agda-lib file, for use with the library
-- management system.

-- Currently the library does not support the JavaScript compiler
-- backend.

------------------------------------------------------------------------
-- Stability guarantees
------------------------------------------------------------------------

-- We do our best to adhere to the spirit of semantic versioning in that
-- minor versions should not break people's code. This applies to the
-- the entire library with one exception: modules with names that end in
-- either ".Core" or ".Primitive".

-- The former have (mostly) been created to avoid mutual recursion
-- between modules and the latter to bind primitive operations to the
-- more efficient operations supplied by the relevant backend.

-- These modules may undergo backwards incompatible changes between
-- minor versions and therefore are imported directly at your own risk.
-- Instead their contents should be accessed by their parent module,
-- whose interface will remain stable.

------------------------------------------------------------------------
-- High-level overview of contents
------------------------------------------------------------------------

-- The top-level module names of the library are currently allocated
-- as follows:
--
-- • Algebra
--     Abstract algebra (monoids, groups, rings etc.), along with
--     properties needed to specify these structures (associativity,
--     commutativity, etc.), and operations on and proofs about the
--     structures.

-- • Axiom
--     Types and consequences of various additional axioms not
--     necessarily included in Agda, e.g. uniqueness of identity
--     proofs, function extensionality and excluded middle.

import README.Axiom

-- • Category
--     Category theory-inspired idioms used to structure functional
--     programs (functors and monads, for instance).

-- • Codata
--     Coinductive data types and properties. There are two different
--     approaches taken. The `Codata` folder contains the new more
--     standard approach using sized types. The `Codata.Musical`
--     folder contains modules using the old musical notation.

-- • Data
--     Data types and properties.

import README.Data

-- • Function
--     Combinators and properties related to functions.

-- • Foreign
--     Related to the foreign function interface.

-- • Induction
--     A general framework for induction (includes lexicographic and
--     well-founded induction).

-- • IO
--     Input/output-related functions.

import README.IO

-- • Level
--     Universe levels.

-- • Reflection
--     Support for reflection.

-- • Relation
--     Properties of and proofs about relations.

-- • Size
--     Sizes used by the sized types mechanism.

-- • Strict
--     Provides access to the builtins relating to strictness.

-- • Tactic
--     Tactics for automatic proof generation

-- ∙ Text
--     Format-based printing, Pretty-printing, and regular expressions


------------------------------------------------------------------------
-- Library design
------------------------------------------------------------------------
-- The following modules contain a discussion of some of the choices
-- that have been made whilst designing the library.

-- • How mathematical hierarchies (e.g. preorder, partial order, total
-- order) are handled in the library.

import README.Design.Hierarchies

-- • How decidability is handled in the library.

import README.Design.Decidability


------------------------------------------------------------------------
-- A selection of useful library modules
------------------------------------------------------------------------

-- Note that module names in source code are often hyperlinked to the
-- corresponding module. In the Emacs mode you can follow these
-- hyperlinks by typing M-. or clicking with the middle mouse button.

-- • Some data types

import Data.Bool     -- Booleans.
import Data.Char     -- Characters.
import Data.Empty    -- The empty type.
import Data.Fin      -- Finite sets.
import Data.List     -- Lists.
import Data.Maybe    -- The maybe type.
import Data.Nat      -- Natural numbers.
import Data.Product  -- Products.
import Data.String   -- Strings.
import Data.Sum      -- Disjoint sums.
import Data.Unit     -- The unit type.
import Data.Vec      -- Fixed-length vectors.

-- • Some co-inductive data types

import Codata.Stream -- Streams.
import Codata.Colist -- Colists.

-- • Some types used to structure computations

import Category.Functor      -- Functors.
import Category.Applicative  -- Applicative functors.
import Category.Monad        -- Monads.

-- • Equality

-- Propositional equality:
import Relation.Binary.PropositionalEquality

-- Convenient syntax for "equational reasoning" using a preorder:
import Relation.Binary.Reasoning.Preorder

-- Solver for commutative ring or semiring equalities:
import Algebra.Solver.Ring

-- • Properties of functions, sets and relations

-- Monoids, rings and similar algebraic structures:
import Algebra

-- Negation, decidability, and similar operations on sets:
import Relation.Nullary

-- Properties of homogeneous binary relations:
import Relation.Binary

-- • Induction

-- An abstraction of various forms of recursion/induction:
import Induction

-- Well-founded induction:
import Induction.WellFounded

-- Various forms of induction for natural numbers:
import Data.Nat.Induction

-- • Support for coinduction

import Codata.Musical.Notation
import Codata.Thunk

-- • IO

import IO

-- ∙ Text

-- Dependently typed formatted printing
import Text.Printf

------------------------------------------------------------------------
-- More documentation
------------------------------------------------------------------------

-- Some examples showing how the case expression can be used.

import README.Case

-- Some examples showing how combinators can be used to emulate
-- "functional reasoning"

import README.Function.Reasoning

-- An example showing how to use the debug tracing mechanism to inspect
-- the behaviour of compiled Agda programs.

import README.Debug.Trace

-- An exploration of the generic programs acting on n-ary functions and
-- n-ary heterogeneous products

import README.Nary

-- Explaining the inspect idiom: use case, equivalent handwritten
-- auxiliary definitions, and implementation details.

import README.Inspect

-- Explaining how to use the automatic solvers

import README.Tactic.MonoidSolver
import README.Tactic.RingSolver

-- Explaining how the Haskell FFI works

import README.Foreign.Haskell

-- Explaining string formats and the behaviour of printf

import README.Text.Printf

-- Showcasing the pretty printing module

import README.Text.Pretty

-- Demonstrating the regular expression matching

import README.Text.Regex

-- Explaining how to display tables of strings:

import README.Text.Tabular

------------------------------------------------------------------------
-- All library modules
------------------------------------------------------------------------

-- For short descriptions of every library module, see Everything;
-- to exclude unsafe modules, see EverythingSafe:

import Everything
import EverythingSafe

-- Note that the Everything* modules are generated automatically. If
-- you have downloaded the library from its Git repository and want
-- to type check README then you can (try to) construct Everything by
-- running "cabal install && GenerateEverything".

-- Note that all library sources are located under src or ffi. The
-- modules README, README.* and Everything are not really part of the
-- library, so these modules are located in the top-level directory
-- instead.
