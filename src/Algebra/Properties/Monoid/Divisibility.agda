------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over monoids
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Monoid)
import Algebra.Properties.Semigroup
open import Level using (_⊔_)
open import Data.Product using (_,_)
open import Relation.Binary

module Algebra.Properties.Monoid.Divisibility {a ℓ} (M : Monoid a ℓ) where

open Monoid M
import Algebra.Divisibility _≈_ _∙_ as Div

------------------------------------------------------------------------
-- Re-export magma divisibility

open import Algebra.Properties.Semigroup.Divisibility semigroup public

------------------------------------------------------------------------
-- Additional properties

ε∣_ : ∀ x → ε ∣ x
ε∣_ = Div.∣-min identityʳ

∣-refl : Reflexive _∣_
∣-refl = Div.∣-refl identityˡ

∣-reflexive : _≈_ ⇒ _∣_
∣-reflexive = Div.∣-reflexive trans identityˡ

∣-isPreorder : IsPreorder _≈_ _∣_
∣-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ∣-reflexive
  ; trans         = ∣-trans
  }

∣-preorder : Preorder a ℓ (a ⊔ ℓ)
∣-preorder = record
  { isPreorder = ∣-isPreorder
  }
