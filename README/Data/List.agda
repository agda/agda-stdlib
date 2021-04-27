------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for the List type
------------------------------------------------------------------------

module README.Data.List where

open import Data.Nat.Base using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

------------------------------------------------------------------------
-- 1. Basics
------------------------------------------------------------------------
-- The `List` datatype is exported by the following file:

open import Data.List
  using
  (List
  ; []; _∷_
  ; sum; map; take; reverse; _++_; drop
  )

-- Lists are built using the "[]" and "_∷_" constructors.

list₁ : List ℕ
list₁ = 3 ∷ 1 ∷ 2 ∷ []

-- Basic operations over lists are also exported by the same file.

lem₁ : sum list₁ ≡ 6
lem₁ = refl

lem₂ : map (_+ 2) list₁ ≡ 5 ∷ 3 ∷ 4 ∷ []
lem₂ = refl

lem₃ : take 2 list₁ ≡ 3 ∷ 1 ∷ []
lem₃ = refl

lem₄ : reverse list₁ ≡ 2 ∷ 1 ∷ 3 ∷ []
lem₄ = refl

lem₅ : list₁ ++ list₁ ≡ 3 ∷ 1 ∷ 2 ∷ 3 ∷ 1 ∷ 2 ∷ []
lem₅ = refl

-- Various basic properties of these operations can be found in:

open import Data.List.Properties

lem₆ : ∀ n (xs : List ℕ) → take n xs ++ drop n xs ≡ xs
lem₆ = take++drop

lem₇ : ∀ (xs : List ℕ) → reverse (reverse xs) ≡ xs
lem₇ = reverse-involutive

lem₈ : ∀ (xs ys zs : List ℕ) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
lem₈ = ++-assoc


------------------------------------------------------------------------
-- 2. Unary relations over lists
------------------------------------------------------------------------

-- Unary relations in `Data.List.Relation.Unary` are used to reason
-- about the properties of an individual list.

------------------------------------------------------------------------
-- Any

-- The predicate `Any` encodes the idea of at least one element of a
-- given list satisfying a given property (or more formally a
-- predicate, see the `Pred` type in `Relation.Unary`).

import README.Data.List.Relation.Unary.Any

------------------------------------------------------------------------
-- All

-- The dual to `Any` is the predicate `All` which encodes the idea that
-- every element in a given list satisfies a given property.

import README.Data.List.Relation.Unary.All

------------------------------------------------------------------------
-- Other unary relations

-- There exist many other unary relations in the
-- `Data.List.Relation.Unary` folder, including:

--    1. lists with every pair of elements related

import Data.List.Relation.Unary.AllPairs

--    2. lists with only unique elements

import Data.List.Relation.Unary.Unique.Setoid

--    3. lists with each pair of neighbouring elements related

import Data.List.Relation.Unary.Linked


------------------------------------------------------------------------
-- 3. Binary relations over lists
------------------------------------------------------------------------

-- Binary relations relate two different lists, and are found in the
-- folder `Data.List.Relation.Binary`.

------------------------------------------------------------------------
-- Pointwise

-- One of the most basic ways to form a binary relation between two
-- lists of type `List A`, given a binary relation over `A`, is to say
-- that two lists are related if they are the same length and:
--   i) the first elements in the lists are related
--   ii) the second elements in the lists are related
--   iii) the third elements in the lists are related etc.
--   etc.

-- This is known as the pointwise lifting of a relation

import README.Data.List.Relation.Binary.Pointwise

------------------------------------------------------------------------
-- Equality

-- There are many different options for what it means for two
-- different lists of type `List A` to be "equal". We will initially
-- consider notions of equality that require the list elements to be
-- pointwise equal.

import README.Data.List.Relation.Binary.Equality

------------------------------------------------------------------------
-- Permutations

-- Alternatively you might consider two lists to be equal if they
-- contain the same elements regardless of the order of the elements.
-- This is known as either "set equality" or a "permutation".

import README.Data.List.Relation.Binary.Permutation

------------------------------------------------------------------------
-- Subsets

-- Instead one might want to order lists by the subset relation which
-- forms a partial order over lists. One list is a subset of another if
-- every element in the first list occurs at least once in the second.

import README.Data.List.Relation.Binary.Subset

------------------------------------------------------------------------
-- Other binary relations

-- There exist many other binary relations in the
-- `Data.List.Relation.Binary` folder, including:

--    1. lexicographic orderings

import Data.List.Relation.Binary.Lex.Strict

--    2. bag/multiset equality

import Data.List.Relation.Binary.BagAndSetEquality

--    3. the sublist relations

import Data.List.Relation.Binary.Sublist.Propositional


------------------------------------------------------------------------
-- 4. Ternary relations over lists
------------------------------------------------------------------------

-- Ternary relations relate three different lists, and are found in the
-- folder `Data.List.Relation.Ternary`.

------------------------------------------------------------------------
-- Interleaving

-- Given two lists, a third list is an `Interleaving` of them if there
-- exists an order preserving partition of it that reconstructs the
-- original two lists.

import README.Data.List.Relation.Ternary.Interleaving


------------------------------------------------------------------------
-- 5. Membership
------------------------------------------------------------------------

-- Although simply a specialisation of the unary predicate `Any`,
-- membership of a list is not strictly a unary or a binary relation
-- over lists. Therefore it lives it it's own top-level folder.

import README.Data.List.Membership
