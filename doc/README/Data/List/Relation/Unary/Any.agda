------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for the `Any` predicate over `List`
------------------------------------------------------------------------

module README.Data.List.Relation.Unary.Any where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (ℕ; _+_; _<_; s≤s; z≤n; _*_; _∸_; _≤_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)

------------------------------------------------------------------------
-- Any

-- The predicate `Any` encodes the idea of at least one element of a
-- given list satisfying a given property (or more formally a
-- predicate, see the `Pred` type in `Relation.Unary`).

open import Data.List.Relation.Unary.Any as Any

-- A proof of type Any consists of a sequence of the "there"
-- constructors, which says that the element lies in the remainder of
-- the list, followed by a single "here" constructor which indicates
-- that the head of the list satisfies the predicate and takes a proof
-- that it does so.

-- For example a proof that a given list of natural numbers contains
-- at least one number greater than or equal to 4 can be written as
-- follows:

lem₁ : Any (4 ≤_) (3 ∷ 5 ∷ 1 ∷ 6 ∷ [])
lem₁ = there (here 4≤5)
  where
  4≤5 = s≤s (s≤s (s≤s (s≤s z≤n)))

-- Note that nothing requires that the proof of `Any` points at the
-- first such element in the list. There is therefore an alternative
-- proof for the above lemma which points to 6 instead of 5.

lem₂ : Any (4 ≤_) (3 ∷ 5 ∷ 1 ∷ 6 ∷ [])
lem₂ = there (there (there (here 4≤6)))
  where
  4≤6 = s≤s (s≤s (s≤s (s≤s z≤n)))

-- There also exist various operations over proofs of `Any` whose names
-- shadow the corresponding list operation. The standard way of using
-- these is to use `as` to name the module:

import Data.List.Relation.Unary.Any as Any

-- and then use the qualified name `Any.map`. For example, map can
-- be used to change the predicate of `Any`:

lem₃ : Any (3 ≤_) (3 ∷ 5 ∷ 1 ∷ 6 ∷ [])
lem₃ = Any.map 4≤x⇒3≤x lem₂
  where
  4≤x⇒3≤x : ∀ {x} → 4 ≤ x → 3 ≤ x
  4≤x⇒3≤x = ≤-trans (n≤1+n 3)

-- Properties of how list functions interact with `Any` can be
-- found in:

import Data.List.Relation.Unary.Any.Properties
