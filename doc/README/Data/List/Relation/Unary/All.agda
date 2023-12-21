------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for the `All` predicate over `List`
------------------------------------------------------------------------

module README.Data.List.Relation.Unary.All where

open import Data.List.Base using ([]; _∷_)
open import Data.Nat using (ℕ; s≤s; z≤n; _≤_)
open import Data.Nat.Properties using (≤-trans; n≤1+n)

------------------------------------------------------------------------
-- All

-- The dual to `Any` is the predicate `All` which encodes the idea that
-- every element in a given list satisfies a given property.

open import Data.List.Relation.Unary.All

-- Proofs for `All` are constructed using exactly the same syntax as
-- is used to construct lists ("[]" & "_∷_"). For example to prove
-- that every element in a list is less than or equal to one:

lem₁ : All (_≤ 1) (1 ∷ 0 ∷ 1 ∷ [])
lem₁ = 1≤1 ∷ 0≤1 ∷ 1≤1 ∷ []
  where
  0≤1 = z≤n
  1≤1 = s≤s z≤n

-- As with `Any`, the module also provides the standard operators
-- `map`, `zip` etc. to manipulate proofs for `All`.

import Data.List.Relation.Unary.All as All

lem₂ : All (_≤ 2) (1 ∷ 0 ∷ 1 ∷ [])
lem₂ = All.map ≤1⇒≤2 lem₁
  where
  ≤1⇒≤2 : ∀ {x} → x ≤ 1 → x ≤ 2
  ≤1⇒≤2 x≤1 = ≤-trans x≤1 (n≤1+n 1)

-- Properties of how list functions interact with `All` can be
-- found in:

import Data.List.Relation.Unary.All.Properties
