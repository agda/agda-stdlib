------------------------------------------------------------------------
-- The Agda standard library
--
-- All library modules, along with short descriptions
------------------------------------------------------------------------

-- Note that core modules are not included.

module EverythingSafe where

-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
import Algebra

-- Solver for equations in commutative monoids
import Algebra.CommutativeMonoidSolver

-- An example of how Algebra.CommutativeMonoidSolver can be used
import Algebra.CommutativeMonoidSolver.Example

-- Properties of functions, such as associativity and commutativity
import Algebra.FunctionProperties

-- Relations between properties of functions, such as associativity and
-- commutativity
import Algebra.FunctionProperties.Consequences

-- Solver for equations in commutative monoids
import Algebra.IdempotentCommutativeMonoidSolver

-- An example of how Algebra.IdempotentCommutativeMonoidSolver can be
-- used
import Algebra.IdempotentCommutativeMonoidSolver.Example

-- Solver for monoid equalities
import Algebra.Monoid-solver

-- Morphisms between algebraic structures
import Algebra.Morphism

-- Some defined operations (multiplication by natural number and
-- exponentiation)
import Algebra.Operations.CommutativeMonoid

-- Some defined operations (multiplication by natural number and
-- exponentiation)
import Algebra.Operations.Semiring

-- Some derivable properties
import Algebra.Properties.AbelianGroup

-- Some derivable properties
import Algebra.Properties.BooleanAlgebra

-- Boolean algebra expressions
import Algebra.Properties.BooleanAlgebra.Expression

-- Some derivable properties
import Algebra.Properties.CommutativeMonoid

-- Some derivable properties
import Algebra.Properties.DistributiveLattice

-- Some derivable properties
import Algebra.Properties.Group

-- Some derivable properties
import Algebra.Properties.Lattice

-- Some derivable properties
import Algebra.Properties.Ring

-- Solver for commutative ring or semiring equalities
import Algebra.RingSolver

-- Commutative semirings with some additional structure ("almost"
-- commutative rings), used by the ring solver
import Algebra.RingSolver.AlmostCommutativeRing

-- Some boring lemmas used by the ring solver
import Algebra.RingSolver.Lemmas

-- Instantiates the ring solver, using the natural numbers as the
-- coefficient "ring"
import Algebra.RingSolver.Natural-coefficients

-- Instantiates the ring solver with two copies of the same ring with
-- decidable equality
import Algebra.RingSolver.Simple

-- Some algebraic structures (not packed up with sets, operations,
-- etc.)
import Algebra.Structures

-- Applicative functors
import Category.Applicative

-- Indexed applicative functors
import Category.Applicative.Indexed

-- Applicative functors on indexed sets (predicates)
import Category.Applicative.Predicate

-- Comonads
import Category.Comonad

-- Functors
import Category.Functor

-- Functors on indexed sets (predicates)
import Category.Functor.Predicate

-- Monads
import Category.Monad

-- A delimited continuation monad
import Category.Monad.Continuation

-- Indexed monads
import Category.Monad.Indexed

-- The partiality monad
import Category.Monad.Partiality

-- An All predicate for the partiality monad
import Category.Monad.Partiality.All

-- Monads on indexed sets (predicates)
import Category.Monad.Predicate

-- The state monad
import Category.Monad.State

-- The Colist type and some operations
import Codata.Colist

-- Bisimilarity for Colists
import Codata.Colist.Bisimilarity

-- Properties of operations on the Colist type
import Codata.Colist.Properties

-- The Conat type and some operations
import Codata.Conat

-- Bisimilarity for Conats
import Codata.Conat.Bisimilarity

-- Properties for Conats
import Codata.Conat.Properties

-- The Covec type and some operations
import Codata.Covec

-- Bisimilarity for Covecs
import Codata.Covec.Bisimilarity

-- Properties of operations on the Covec type
import Codata.Covec.Properties

-- The Delay type and some operations
import Codata.Delay

-- Bisimilarity for the Delay type
import Codata.Delay.Bisimilarity

-- A categorical view of Delay
import Codata.Delay.Categorical

-- Properties of operations on the Delay type
import Codata.Delay.Properties

-- "Finite" sets indexed on coinductive "natural" numbers
import Codata.Musical.Cofin

-- Coinductive lists
import Codata.Musical.Colist

-- Infinite merge operation for coinductive lists
import Codata.Musical.Colist.Infinite-merge

-- Coinductive "natural" numbers
import Codata.Musical.Conat

-- Costrings
import Codata.Musical.Costring

-- Coinductive vectors
import Codata.Musical.Covec

-- M-types (the dual of W-types)
import Codata.Musical.M

-- Indexed M-types (the dual of indexed W-types aka Petersson-Synek
-- trees).
import Codata.Musical.M.Indexed

-- Streams
import Codata.Musical.Stream

-- The Stream type and some operations
import Codata.Stream

-- Bisimilarity for Streams
import Codata.Stream.Bisimilarity

-- A categorical view of Stream
import Codata.Stream.Categorical

-- Properties of operations on the Stream type
import Codata.Stream.Properties

-- The Thunk wrappers for sized codata, copredicates and corelations
import Codata.Thunk

-- Basic types related to coinduction
import Coinduction

-- AVL trees
import Data.AVL

-- Types and functions which are used to keep track of height
-- invariants in AVL Trees
import Data.AVL.Height

-- Indexed AVL trees
import Data.AVL.Indexed

-- Finite maps with indexed keys and values, based on AVL trees
import Data.AVL.IndexedMap

-- Keys for AVL trees
-- The key type extended with a new minimum and maximum.
import Data.AVL.Key

-- Finite sets, based on AVL trees
import Data.AVL.Sets

-- A binary representation of natural numbers
import Data.Bin

-- Properties of the binary representation of natural numbers
import Data.Bin.Properties

-- Booleans
import Data.Bool

-- The type for booleans and some operations
import Data.Bool.Base

-- A bunch of properties
import Data.Bool.Properties

-- Showing booleans
import Data.Bool.Show

-- Bounded vectors
import Data.BoundedVec

-- Bounded vectors (inefficient, concrete implementation)
import Data.BoundedVec.Inefficient

-- Characters
import Data.Char

-- Basic definitions for Characters
import Data.Char.Base

-- Containers, based on the work of Abbott and others
import Data.Container

-- Properties related to ◇
import Data.Container.Any

-- Container combinators
import Data.Container.Combinator

-- The free monad construction on containers
import Data.Container.FreeMonad

-- Indexed containers aka interaction structures aka polynomial
-- functors. The notation and presentation here is closest to that of
-- Hancock and Hyvernat in "Programming interfaces and basic topology"
-- (2006/9).
import Data.Container.Indexed

-- Indexed container combinators
import Data.Container.Indexed.Combinator

-- The free monad construction on indexed containers
import Data.Container.Indexed.FreeMonad

-- Lists with fast append
import Data.DifferenceList

-- Natural numbers with fast addition (for use together with
-- DifferenceVec)
import Data.DifferenceNat

-- Vectors with fast append
import Data.DifferenceVec

-- Digits and digit expansions
import Data.Digit

-- Empty type
import Data.Empty

-- An irrelevant version of ⊥-elim
import Data.Empty.Irrelevant

-- Finite sets
import Data.Fin

-- Decision procedures for finite sets and subsets of finite sets
import Data.Fin.Dec

-- Bijections on finite sets (i.e. permutations).
import Data.Fin.Permutation

-- Component functions of permutations found in `Data.Fin.Permutation`
import Data.Fin.Permutation.Components

-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
import Data.Fin.Properties

-- Subsets of finite sets
import Data.Fin.Subset

-- Some properties about subsets
import Data.Fin.Subset.Properties

-- Substitutions
import Data.Fin.Substitution

-- An example of how Data.Fin.Substitution can be used: a definition
-- of substitution for the untyped λ-calculus, along with some lemmas
import Data.Fin.Substitution.Example

-- Substitution lemmas
import Data.Fin.Substitution.Lemmas

-- Application of substitutions to lists, along with various lemmas
import Data.Fin.Substitution.List

-- Floats
import Data.Float

-- Directed acyclic multigraphs
import Data.Graph.Acyclic

-- Integers
import Data.Integer

-- Properties related to addition of integers
import Data.Integer.Addition.Properties

-- Integers, basic types and operations
import Data.Integer.Base

-- Divisibility and coprimality
import Data.Integer.Divisibility

-- Properties related to multiplication of integers
import Data.Integer.Multiplication.Properties

-- Some properties about integers
import Data.Integer.Properties

-- Lists
import Data.List

-- Lists where all elements satisfy a given property
import Data.List.All

-- Properties related to All
import Data.List.All.Properties

-- Lists where at least one element satisfies a given property
import Data.List.Any

-- Properties related to Any
import Data.List.Any.Properties

-- Lists, basic types and operations
import Data.List.Base

-- A categorical view of List
import Data.List.Categorical

-- A data structure which keeps track of an upper bound on the number
-- of elements /not/ in a given list
import Data.List.Countdown

-- Decidable propositional membership over lists
import Data.List.Membership.DecPropositional

-- Decidable setoid membership over lists
import Data.List.Membership.DecSetoid

-- Data.List.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
import Data.List.Membership.Propositional

-- Properties related to propositional list membership
import Data.List.Membership.Propositional.Properties

-- List membership and some related definitions
import Data.List.Membership.Setoid

-- Properties related to setoid list membership
import Data.List.Membership.Setoid.Properties

-- Non-empty lists
import Data.List.NonEmpty

-- A categorical view of List⁺
import Data.List.NonEmpty.Categorical

-- Properties of non-empty lists
import Data.List.NonEmpty.Properties

-- List-related properties
import Data.List.Properties

-- Bag and set equality
import Data.List.Relation.BagAndSetEquality

-- Decidable equality over lists using propositional equality
import Data.List.Relation.Equality.DecPropositional

-- Decidable equality over lists parameterised by some setoid
import Data.List.Relation.Equality.DecSetoid

-- Equality over lists using propositional equality
import Data.List.Relation.Equality.Propositional

-- Equality over lists parameterised by some setoid
import Data.List.Relation.Equality.Setoid

-- Lexicographic ordering of lists
import Data.List.Relation.Lex.NonStrict

-- Lexicographic ordering of lists
import Data.List.Relation.Lex.Strict

-- An inductive definition for the permutation relation
import Data.List.Relation.Permutation.Inductive

-- Properties of permutation
import Data.List.Relation.Permutation.Inductive.Properties

-- Pointwise lifting of relations to lists
import Data.List.Relation.Pointwise

-- The sublist relation over propositional equality.
import Data.List.Relation.Sublist.Extensional.Propositional

-- Properties of the sublist relation over setoid equality.
import Data.List.Relation.Sublist.Extensional.Propositional.Properties

-- The extensional sublist relation over setoid equality.
import Data.List.Relation.Sublist.Extensional.Setoid

-- Properties of the extensional sublist relation over setoid equality.
import Data.List.Relation.Sublist.Extensional.Setoid.Properties

-- An inductive definition of sublist. This commonly known as an Order
-- Preserving Embedding (OPE).
import Data.List.Relation.Sublist.Inductive

-- Reverse view
import Data.List.Reverse

-- List Zippers, basic types and operations
import Data.List.Zipper

-- List Zipper-related properties
import Data.List.Zipper.Properties

-- The Maybe type
import Data.Maybe

-- The Maybe type and some operations
import Data.Maybe.Base

-- A categorical view of Maybe
import Data.Maybe.Categorical

-- Natural numbers
import Data.Nat

-- Natural numbers, basic types and operations
import Data.Nat.Base

-- Coprimality
import Data.Nat.Coprimality

-- Integer division
import Data.Nat.DivMod

-- Divisibility
import Data.Nat.Divisibility

-- Greatest common divisor
import Data.Nat.GCD

-- Boring lemmas used in Data.Nat.GCD and Data.Nat.Coprimality
import Data.Nat.GCD.Lemmas

-- A generalisation of the arithmetic operations
import Data.Nat.GeneralisedArithmetic

-- Definition of and lemmas related to "true infinitely often"
import Data.Nat.InfinitelyOften

-- Least common multiple
import Data.Nat.LCM

-- Primality
import Data.Nat.Primality

-- A bunch of properties about natural number operations
import Data.Nat.Properties

-- A bunch of properties about natural number operations
import Data.Nat.Properties.Simple

-- Showing natural numbers
import Data.Nat.Show

-- Transitive closures
import Data.Plus

-- Products
import Data.Product

-- Universe-sensitive functor and monad instances for the Product type.
import Data.Product.Categorical

-- N-ary products
import Data.Product.N-ary

-- A categorical view of N-ary products
import Data.Product.N-ary.Categorical

-- Properties of n-ary products
import Data.Product.N-ary.Properties

-- Properties of products
import Data.Product.Properties

-- Lexicographic products of binary relations
import Data.Product.Relation.Lex.NonStrict

-- Lexicographic products of binary relations
import Data.Product.Relation.Lex.Strict

-- Pointwise lifting of binary relations to sigma types
import Data.Product.Relation.Pointwise.Dependent

-- Pointwise products of binary relations
import Data.Product.Relation.Pointwise.NonDependent

-- Rational numbers
import Data.Rational

-- Properties of Rational numbers
import Data.Rational.Properties

-- Reflexive closures
import Data.ReflexiveClosure

-- Signs
import Data.Sign

-- Some properties about signs
import Data.Sign.Properties

-- The reflexive transitive closures of McBride, Norell and Jansson
import Data.Star

-- Bounded vectors (inefficient implementation)
import Data.Star.BoundedVec

-- Decorated star-lists
import Data.Star.Decoration

-- Environments (heterogeneous collections)
import Data.Star.Environment

-- Finite sets defined using the reflexive-transitive closure, Star
import Data.Star.Fin

-- Lists defined in terms of the reflexive-transitive closure, Star
import Data.Star.List

-- Natural numbers defined using the reflexive-transitive closure, Star
import Data.Star.Nat

-- Pointers into star-lists
import Data.Star.Pointer

-- Some properties related to Data.Star
import Data.Star.Properties

-- Vectors defined in terms of the reflexive-transitive closure, Star
import Data.Star.Vec

-- Strings
import Data.String

-- Strings
import Data.String.Base

-- Sums (disjoint unions)
import Data.Sum

-- Sums (disjoint unions)
import Data.Sum.Base

-- Universe-sensitive functor and monad instances for the Sum type.
import Data.Sum.Categorical

-- Properties of sums (disjoint unions)
import Data.Sum.Properties

-- Sums of binary relations
import Data.Sum.Relation.LeftOrder

-- Pointwise sum
import Data.Sum.Relation.Pointwise

-- Fixed-size tables of values, implemented as functions from 'Fin n'.
-- Similar to 'Data.Vec', but focusing on ease of retrieval instead of
-- ease of adding and removing elements.
import Data.Table

-- Tables, basic types and operations
import Data.Table.Base

-- Table-related properties
import Data.Table.Properties

-- Pointwise table equality
import Data.Table.Relation.Equality

-- An either-or-both data type
import Data.These

-- Some unit types
import Data.Unit

-- The unit type and the total relation on unit
import Data.Unit.Base

-- Some unit types
import Data.Unit.NonEta

-- Vectors
import Data.Vec

-- Vectors where all elements satisfy a given property
import Data.Vec.All

-- Properties related to All
import Data.Vec.All.Properties

-- Vectors where at least one element satisfies a given property
import Data.Vec.Any

-- A categorical view of Vec
import Data.Vec.Categorical

-- Membership of vectors based on propositional equality,
-- along with some additional definitions.
import Data.Vec.Membership.Propositional

-- Properties of membership of vectors based on propositional equality.
import Data.Vec.Membership.Propositional.Properties

-- Code for converting Vec A n → B to and from n-ary functions
import Data.Vec.N-ary

-- Some Vec-related properties
import Data.Vec.Properties

-- Decidable vector equality over propositional equality
import Data.Vec.Relation.Equality.DecPropositional

-- Decidable semi-heterogeneous vector equality over setoids
import Data.Vec.Relation.Equality.DecSetoid

-- Vector equality over propositional equality
import Data.Vec.Relation.Equality.Propositional

-- Semi-heterogeneous vector equality over setoids
import Data.Vec.Relation.Equality.Setoid

-- Extensional pointwise lifting of relations to vectors
import Data.Vec.Relation.Pointwise.Extensional

-- Inductive pointwise lifting of relations to vectors
import Data.Vec.Relation.Pointwise.Inductive

-- W-types
import Data.W

-- Indexed W-types aka Petersson-Synek trees
import Data.W.Indexed

-- Machine words
import Data.Word

-- Type(s) used (only) when calling out to Haskell via the FFI
import Foreign.Haskell

-- Simple combinators working solely on and with functions
import Function

-- Bijections
import Function.Bijection

-- Function setoids and related constructions
import Function.Equality

-- Equivalence (coinhabitance)
import Function.Equivalence

-- A categorical view of the identity function
import Function.Identity.Categorical

-- Injections
import Function.Injection

-- Inverses
import Function.Inverse

-- Left inverses
import Function.LeftInverse

-- A module used for creating function pipelines, see
-- README.Function.Reasoning for examples
import Function.Reasoning

-- A universe which includes several kinds of "relatedness" for sets,
-- such as equivalences, surjections and bijections
import Function.Related

-- Basic lemmas showing that various types are related (isomorphic or
-- equivalent or…)
import Function.Related.TypeIsomorphisms

-- Surjections
import Function.Surjection

-- IO
-- import IO

-- Primitive IO: simple bindings to Haskell types and functions
-- import IO.Primitive

-- An abstraction of various forms of recursion/induction
import Induction

-- Lexicographic induction
import Induction.Lexicographic

-- Various forms of induction for natural numbers
import Induction.Nat

-- Well-founded induction
import Induction.WellFounded

-- Universe levels
import Level

-- Conversion from naturals to universe levels
import Level.Literals

-- Record types with manifest fields and "with", based on Randy
-- Pollack's "Dependently Typed Records in Type Theory"
import Record

-- Support for reflection
-- import Reflection

-- Properties of homogeneous binary relations
import Relation.Binary

-- Equivalence closures of binary relations
import Relation.Binary.Closure.Equivalence

-- Reflexive closures
import Relation.Binary.Closure.Reflexive

-- The reflexive transitive closures of McBride, Norell and Jansson
import Relation.Binary.Closure.ReflexiveTransitive

-- Some properties related to Data.Star
import Relation.Binary.Closure.ReflexiveTransitive.Properties

-- Symmetric closures of binary relations
import Relation.Binary.Closure.Symmetric

-- Transitive closures
import Relation.Binary.Closure.Transitive

-- Some properties imply others
import Relation.Binary.Consequences

-- Convenient syntax for equational reasoning
import Relation.Binary.EqReasoning

-- Equivalence closures of binary relations
import Relation.Binary.EquivalenceClosure

-- Many properties which hold for _∼_ also hold for flip _∼_
import Relation.Binary.Flip

-- Heterogeneous equality
import Relation.Binary.HeterogeneousEquality

-- Quotients for Heterogeneous equality
import Relation.Binary.HeterogeneousEquality.Quotients

-- Example of a Quotient: ℤ as (ℕ × ℕ / ~)
import Relation.Binary.HeterogeneousEquality.Quotients.Examples

-- Indexed binary relations
import Relation.Binary.Indexed

-- Homogeneously-indexed binary relations
import Relation.Binary.Indexed.Homogeneous

-- Induced preorders
import Relation.Binary.InducedPreorders

-- Order-theoretic lattices
import Relation.Binary.Lattice

-- Lexicographic ordering of lists
import Relation.Binary.List.NonStrictLex

-- Pointwise lifting of relations to lists
import Relation.Binary.List.Pointwise

-- Lexicographic ordering of lists
import Relation.Binary.List.StrictLex

-- Conversion of _≤_ to _<_
import Relation.Binary.NonStrictToStrict

-- Many properties which hold for _∼_ also hold for _∼_ on f
import Relation.Binary.On

-- Order morphisms
import Relation.Binary.OrderMorphism

-- Convenient syntax for "equational reasoning" using a partial order
import Relation.Binary.PartialOrderReasoning

-- Convenient syntax for "equational reasoning" using a preorder
import Relation.Binary.PreorderReasoning

-- Lexicographic products of binary relations
import Relation.Binary.Product.NonStrictLex

-- Pointwise products of binary relations
import Relation.Binary.Product.Pointwise

-- Lexicographic products of binary relations
import Relation.Binary.Product.StrictLex

-- Properties satisfied by bounded join semilattices
import Relation.Binary.Properties.BoundedJoinSemilattice

-- Properties satisfied by bounded meet semilattices
import Relation.Binary.Properties.BoundedMeetSemilattice

-- Properties satisfied by decidable total orders
import Relation.Binary.Properties.DecTotalOrder

-- Properties satisfied by join semilattices
import Relation.Binary.Properties.JoinSemilattice

-- Properties satisfied by lattices
import Relation.Binary.Properties.Lattice

-- Properties satisfied by meet semilattices
import Relation.Binary.Properties.MeetSemilattice

-- Properties satisfied by posets
import Relation.Binary.Properties.Poset

-- Properties satisfied by preorders
import Relation.Binary.Properties.Preorder

-- Properties satisfied by strict partial orders
import Relation.Binary.Properties.StrictPartialOrder

-- Properties satisfied by strict partial orders
import Relation.Binary.Properties.StrictTotalOrder

-- Properties satisfied by total orders
import Relation.Binary.Properties.TotalOrder

-- Propositional (intensional) equality
import Relation.Binary.PropositionalEquality

-- An equality postulate which evaluates
-- import Relation.Binary.PropositionalEquality.TrustMe

-- Helpers intended to ease the development of "tactics" which use
-- proof by reflection
import Relation.Binary.Reflection

-- Convenient syntax for "equational reasoning" in multiple Setoids
import Relation.Binary.SetoidReasoning

-- Pointwise lifting of binary relations to sigma types
import Relation.Binary.Sigma.Pointwise

-- Some simple binary relations
import Relation.Binary.Simple

-- Convenient syntax for "equational reasoning" using a strict partial
-- order
import Relation.Binary.StrictPartialOrderReasoning

-- Conversion of < to ≤, along with a number of properties
import Relation.Binary.StrictToNonStrict

-- Sums of binary relations
import Relation.Binary.Sum

-- Symmetric closures of binary relations
import Relation.Binary.SymmetricClosure

-- This module is DEPRECATED.
import Relation.Binary.Vec.Pointwise

-- Operations on nullary relations (like negation and decidability)
import Relation.Nullary

-- Operations on and properties of decidable relations
import Relation.Nullary.Decidable

-- Implications of nullary relations
import Relation.Nullary.Implication

-- Properties related to negation
import Relation.Nullary.Negation

-- Products of nullary relations
import Relation.Nullary.Product

-- Sums of nullary relations
import Relation.Nullary.Sum

-- A universe of proposition functors, along with some properties
import Relation.Nullary.Universe

-- Unary relations
import Relation.Unary

-- Predicate transformers
import Relation.Unary.PredicateTransformer

-- Properties of constructions over unary relations
import Relation.Unary.Properties

-- Sizes for Agda's sized types
import Size

-- Strictness combinators
import Strict

-- Universes
import Universe
