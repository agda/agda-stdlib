module README where

------------------------------------------------------------------------
-- The Agda standard library, version 1.2-dev
--
-- Authors: Nils Anders Danielsson, Matthew Daggitt, Guillaume Allais
-- with contributions from Andreas Abel, Stevan Andjelkovic,
-- Jean-Philippe Bernardy, Peter Berry, Bradley Hardy Joachim Breitner,
-- Samuel Bronson, Daniel Brown, James Chapman, Liang-Ting Chen,
-- Dominique Devriese, Dan Doel, Érdi Gergő, Zack Grannan,
-- Helmut Grohne, Simon Foster, Liyang Hu, Jason Hu, Patrik Jansson,
-- Alan Jeffrey, Wen Kokke, Evgeny Kotelnikov, Sergei Meshveliani,
-- Eric Mertens, Darin Morrison, Guilhem Moulin, Shin-Cheng Mu,
-- Ulf Norell, Noriyuki Ohkawa, Nicolas Pouillard,
-- Andrés Sicard-Ramírez, Lex van der Stoep, Sandro Stucki, Milo Turner,
-- Noam Zeilberger and other anonymous contributors.
------------------------------------------------------------------------

-- This version of the library has been tested using Agda 2.6.0.1.

-- The library comes with a .agda-lib file, for use with the library
-- management system.

-- Currently the library does not support the JavaScript compiler
-- backend.

------------------------------------------------------------------------
-- Module hierarchy
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

------------------------------------------------------------------------
-- Record hierarchies
------------------------------------------------------------------------

-- When an abstract hierarchy of some sort (for instance semigroup →
-- monoid → group) is included in the library the basic approach is to
-- specify the properties of every concept in terms of a record
-- containing just properties, parameterised on the underlying
-- operations, sets etc.:
--
--   record IsSemigroup {A} (≈ : Rel A) (∙ : Op₂ A) : Set where
--     open FunctionProperties ≈
--     field
--       isEquivalence : IsEquivalence ≈
--       assoc         : Associative ∙
--       ∙-cong        : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈
--
-- More specific concepts are then specified in terms of the simpler
-- ones:
--
--     record IsMonoid {A} (≈ : Rel A) (∙ : Op₂ A) (ε : A) : Set where
--       open FunctionProperties ≈
--       field
--         isSemigroup : IsSemigroup ≈ ∙
--         identity    : Identity ε ∙
--
--     open IsSemigroup isSemigroup public
--
-- Note here that `open IsSemigroup isSemigroup public` ensures that the
-- fields of the isSemigroup record can be accessed directly; this
-- technique enables the user of an IsMonoid record to use underlying
-- records without having to manually open an entire record hierarchy.
-- This is not always possible, though. Consider the following definition
-- of preorders:
--
--   record IsPreorder {A : Set}
--                     (_≈_ : Rel A) -- The underlying equality.
--                     (_∼_ : Rel A) -- The relation.
--                     : Set where
--     field
--       isEquivalence : IsEquivalence _≈_
--       -- Reflexivity is expressed in terms of an underlying equality:
--       reflexive     : _≈_ ⇒ _∼_
--       trans         : Transitive _∼_
--
--     module Eq = IsEquivalence isEquivalence
--
--     ...
--
-- The Eq module in IsPreorder is not opened publicly, because it
-- contains some fields which clash with fields or other definitions
-- in IsPreorder.

-- Records packing up properties with the corresponding operations,
-- sets, etc. are also defined:
--
--   record Semigroup : Set₁ where
--     infixl 7 _∙_
--     infix  4 _≈_
--     field
--       Carrier     : Set
--       _≈_         : Rel Carrier
--       _∙_         : Op₂ Carrier
--       isSemigroup : IsSemigroup _≈_ _∙_
--
--     open IsSemigroup isSemigroup public
--
--     setoid : Setoid
--     setoid = record { isEquivalence = isEquivalence }
--
--   record Monoid : Set₁ where
--     infixl 7 _∙_
--     infix  4 _≈_
--     field
--       Carrier  : Set
--       _≈_      : Rel Carrier
--       _∙_      : Op₂ Carrier
--       ε        : Carrier
--       isMonoid : IsMonoid _≈_ _∙_ ε
--
--     open IsMonoid isMonoid public
--
--     semigroup : Semigroup
--     semigroup = record { isSemigroup = isSemigroup }
--
--     open Semigroup semigroup public using (setoid)
--
-- Note that the Monoid record does not include a Semigroup field.
-- Instead the Monoid /module/ includes a "repackaging function"
-- semigroup which converts a Monoid to a Semigroup.

-- The above setup may seem a bit complicated, but we think it makes the
-- library quite easy to work with, while also providing enough
-- flexibility.

------------------------------------------------------------------------
-- More documentation
------------------------------------------------------------------------

-- Examples of how decidability is handled in the library.

import README.Decidability

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

-- Explaining string formats and the behaviour of printf

import README.Text

------------------------------------------------------------------------
-- Core modules
------------------------------------------------------------------------

-- Some modules have names ending in ".Core". These modules are
-- internal, and have (mostly) been created to avoid mutual recursion
-- between modules. They should not be imported directly; their
-- contents are reexported by other modules.

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
