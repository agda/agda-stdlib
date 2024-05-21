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

open import Algebra.Bundles using (Monoid)
open import Algebra.Structures using (IsMonoid)
open import Data.List.Base using (List; []; _++_)
import Data.List.Properties as List
import Data.List.Relation.Binary.Equality.Setoid as ≋
open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Level using (_⊔_)

open ≋ S using (_≋_; ≋-refl; ≋-reflexive; ≋-isEquivalence; ++⁺)

------------------------------------------------------------------------
-- The []-++-Monoid

-- Structure

isMonoid : IsMonoid _≋_ _++_ []
isMonoid = record
  { isSemigroup = record
    { isMagma = record
      { isEquivalence = ≋-isEquivalence
      ; ∙-cong = ++⁺
      }
    ; assoc = λ xs ys zs → ≋-reflexive (List.++-assoc xs ys zs)
    }
  ; identity = (λ _ → ≋-refl) , ≋-reflexive ∘ List.++-identityʳ
  }

-- Bundle

monoid : Monoid c (c ⊔ ℓ)
monoid = record { isMonoid = isMonoid }
