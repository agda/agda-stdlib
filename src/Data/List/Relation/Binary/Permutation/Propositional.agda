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
import Data.List.Relation.Binary.Permutation.Homogeneous.Properties.Core as Core

------------------------------------------------------------------------
-- Definition of permutation

private
  module ↭ = Permutation (setoid A)

-- Note that this is now defined in terms of `Permutation.Setoid` (#2317)

open ↭ public
  hiding ( ↭-reflexive; ↭-pointwise; ↭-trans; ↭-isEquivalence
         ; module PermutationReasoning; ↭-setoid
         )

------------------------------------------------------------------------
-- _↭_ is an equivalence

↭-reflexive : _≡_ ⇒ _↭_
↭-reflexive refl = ↭-refl

↭-pointwise : _≋_ ⇒ _↭_
↭-pointwise xs≋ys = ↭-reflexive (≋⇒≡ xs≋ys)

-- A smart version of trans that avoids unnecessary `refl`s (see #1113).
↭-transˡ-≋ : LeftTrans _≋_ _↭_
↭-transˡ-≋ xs≋ys ys↭zs with refl ← ≋⇒≡ xs≋ys = ys↭zs

↭-transʳ-≋ : RightTrans _↭_ _≋_
↭-transʳ-≋ xs↭ys ys≋zs with refl ← ≋⇒≡ ys≋zs = xs↭ys

↭-trans : Transitive _↭_
↭-trans = Core.LRTransitivity.↭-trans ↭-transˡ-≋ ↭-transʳ-≋

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
-- see `Data.List.Relation.Binary.Permutation.Setoid.↭-Reasoning`. 

module PermutationReasoning = ↭-Reasoning ↭-isEquivalence ↭-pointwise

------------------------------------------------------------------------
-- Bundle export

open PermutationReasoning public using (↭-setoid)
