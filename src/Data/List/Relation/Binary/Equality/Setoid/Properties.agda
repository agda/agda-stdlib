------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of List modulo ≋
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Binary.Equality.Setoid.Properties
  {c ℓ} (S : Setoid c ℓ)
  where

open import Algebra.Bundles using (Magma; Semigroup; Monoid)
import Algebra.Structures as Structures
open import Data.List.Base using (List; []; _++_)
import Data.List.Properties as List
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Level using (_⊔_)

open ≋ S using (_≋_; ≋-refl; ≋-reflexive; ≋-isEquivalence; ++⁺)
open Structures _≋_ using (IsMagma; IsSemigroup; IsMonoid)

------------------------------------------------------------------------
-- The []-++-Monoid

-- Structures

isMagma : IsMagma _++_
isMagma = record
  { isEquivalence = ≋-isEquivalence
  ; ∙-cong = ++⁺
  }

isSemigroup : IsSemigroup _++_
isSemigroup = record
  { isMagma = isMagma
  ; assoc = λ xs ys zs → ≋-reflexive (List.++-assoc xs ys zs)
  }

isMonoid : IsMonoid _++_ []
isMonoid = record
  { isSemigroup = isSemigroup
  ; identity = (λ _ → ≋-refl) , ≋-reflexive ∘ List.++-identityʳ
  }

-- Bundles

magma : Magma c (c ⊔ ℓ)
magma = record { isMagma = isMagma }

semigroup : Semigroup c (c ⊔ ℓ)
semigroup = record { isSemigroup = isSemigroup }

monoid : Monoid c (c ⊔ ℓ)
monoid = record { isMonoid = isMonoid }
