------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition for the permutation relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Permutation.Propositional
  {a} {A : Set a} where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Binary.Equality.Propositional using (_≋_; ≋⇒≡)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions
  using (Reflexive; Transitive; LeftTrans; RightTrans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; setoid)

import Data.List.Relation.Binary.Permutation.Setoid as Permutation


------------------------------------------------------------------------
-- An inductive definition of permutation

-- Note that one would expect that this would be defined in terms of
-- `Permutation.Setoid`. This is not currently the case as it involves
-- adding in a bunch of trivial `_≡_` proofs to the constructors which
-- a) adds noise and b) prevents easy access to the variables `x`, `y`.
-- This may be changed in future when a better solution is found.
{-
infix 3 _↭_

data _↭_ : Rel (List A) a where
  refl  : ∀ {xs}        → xs ↭ xs
  prep  : ∀ {xs ys} x   → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ {xs ys} x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans : ∀ {xs ys zs}  → xs ↭ ys → ys ↭ zs → xs ↭ zs
-}
open module ↭ = Permutation (setoid A) public
  hiding ( ↭-reflexive; ↭-pointwise; ↭-trans
         ; ↭-isEquivalence; ↭-setoid; module PermutationReasoning
         )


------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = ↭-refl

↭-pointwise : _≋_ ⇒ _↭_
↭-pointwise xs≋ys = ↭-reflexive (≋⇒≡ xs≋ys)

-- A smart version of trans that avoids unnecessary `refl`s (see #1113).
↭-trans : Transitive _↭_
↭-trans = ↭-trans′ ↭-transˡ-≋ ↭-transʳ-≋
  where
  ↭-transˡ-≋ : LeftTrans _≋_ _↭_
  ↭-transˡ-≋ xs≋ys ys↭zs with refl ← ≋⇒≡ xs≋ys = ys↭zs

  ↭-transʳ-≋ : RightTrans _↭_ _≋_
  ↭-transʳ-≋ xs↭ys ys≋zs with refl ← ≋⇒≡ ys≋zs = xs↭ys

↭-isEquivalence : IsEquivalence _↭_
↭-isEquivalence = record
  { refl  = ↭-refl
  ; sym   = ↭-sym
  ; trans = ↭-trans
  }

------------------------------------------------------------------------
-- A reasoning API to chain permutation proofs and allow "zooming in"
-- to localised reasoning. For details of the axiomatisation, and
-- in particular the refactored dependencies,
-- see `Data.List.Relation.Binary.Permutation.Setoid`

module PermutationReasoning = ↭-Reasoning ↭-isEquivalence ↭-pointwise

------------------------------------------------------------------------
-- Bundle export

open PermutationReasoning public using (↭-setoid)
