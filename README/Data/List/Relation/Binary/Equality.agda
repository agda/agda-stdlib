------------------------------------------------------------------------
-- The Agda standard library
--
-- Documentation for pointwise equality over `List`s
------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

module README.Data.List.Relation.Binary.Equality where

open import Data.Nat using (ℕ; _+_; _<_; s≤s; z≤n; _*_; _∸_; _≤_)
open import Data.Nat.Properties as NatProp
open import Data.List.Base
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; setoid)

------------------------------------------------------------------------
-- Pointwise equality

-- There are many different options for what it means for two
-- different lists of type `List A` to be "equal". Here we will
-- consider "pointwise" equality that requires the lists to be the
-- same length and every pair of elements to be "equal".

-- The most basic option is simply to use propositional equality
-- `_≡_` over lists:

open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; refl)

lem₁ : 1 ∷ 2 ∷ 3 ∷ [] ≡ 1 ∷ 2 ∷ 3 ∷ []
lem₁ = refl

-- However propositional equality is only suitable when we want to
-- use propositional equality to compare the individual elements.
-- Although a contrived example, consider trying to prove the
-- equality of two lists of the type `List (ℕ → ℕ)`:

lem₂ : (λ x → 2 * x + 2) ∷ [] ≡ (λ x → 2 * (x + 1)) ∷ []
lem₂ = {!!}

-- In such a case it is impossible to prove the two lists equal with
-- refl as the two functions are not propositionally equal. In the
-- absence of postulating function extensionality (see README.Axioms),
-- the most common definition of function equality is to say that two
-- functions are equal if their outputs are always propositionally
-- equal for any input. This notion of function equality `_≗_` is
-- found in:

open import Relation.Binary.PropositionalEquality using (_≗_)

-- We now want to use the `Pointwise` relation to say that the two
-- lists are equal if their elements are pointwise equal with resepct
-- to `_≗_`. However instead of using the pointwise module directly
-- to write:

open import Data.List.Relation.Binary.Pointwise using (Pointwise)

lem₃ : Pointwise _≗_ ((λ x → x + 1) ∷ []) ((λ x → x + 2 ∸ 1) ∷ [])
lem₃ = {!!}

-- the library provides some nicer wrappers and infix notation in the
-- folder "Data.List.Relation.Binary.Equality".

-- Within this folder there are four different modules.

import Data.List.Relation.Binary.Equality.Setoid           as SetoidEq
import Data.List.Relation.Binary.Equality.DecSetoid        as DecSetoidEq
import Data.List.Relation.Binary.Equality.Propositional    as PropEq
import Data.List.Relation.Binary.Equality.DecPropositional as DecPropEq

-- Which one should be used depends on whether the underlying equality
-- over "A" is:
--   i)  propositional or setoid-based
--   ii) decidable.

-- Each of the modules except `PropEq` are designed to be opened with a
-- module parameter. This is to avoid having to specify the underlying
-- equality relation or the decidability proofs every time you use the
-- list equality.

-- In our example function equality is not decidable and not propositional
-- and so we want to use the `SetoidEq` module. This requires a proof that
-- the `_≗_` relation forms a setoid over functions of the type `ℕ → ℕ`.
-- This is found in:

open import Relation.Binary.PropositionalEquality using (_→-setoid_)

-- The `SetoidEq` module should therefore be opened as follows:

open SetoidEq (ℕ →-setoid ℕ)

-- All four equality modules provide an infix operator `_≋_` for the
-- new equality relation over lists. The type of `lem₃` can therefore
-- be rewritten as:

lem₄ : (λ x → x + 1) ∷ [] ≋ (λ x → x + 2 ∸ 1) ∷ []
lem₄ = 2x+2≗2[x+1] ∷ []
  where
  2x+2≗2[x+1] : (λ x → x + 1) ≗ (λ x → x + 2 ∸ 1)
  2x+2≗2[x+1] x = sym (+-∸-assoc x (s≤s z≤n))

-- The modules also provide proofs that the `_≋_` relation is a
-- setoid in its own right and therefore is reflexive, symmetric,
-- transitive:

lem₅ : (λ x → 2 * x + 2) ∷ [] ≋ (λ x → 2 * x + 2) ∷ []
lem₅ = ≋-refl

-- If we could prove that `_≗_` forms a `DecSetoid` then we could use
-- the module `DecSetoidEq` instead. This exports everything from
-- `SetoidEq` as well as the additional proof `_≋?_` that the list
-- equality is decidable.

-- This pattern of four modules for each of the four different types
-- of equality is repeated throughout the library (e.g. see the
-- `Membership`). Note that in this case the modules `PropEq` and
-- `DecPropEq` are not very useful as if two lists are pointwise
-- propositionally equal they are necessarily propositionally equal
-- (and vice-versa). There are proofs of this fact exported by
-- `PropEq` and `DecPropEq`. Although, these two types of list equality
-- are not very useful in practice, they are included for completeness's
-- sake.
