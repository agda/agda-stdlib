------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of divisibility over monoids
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Monoid)
open import Data.Product using (_,_)
open import Relation.Binary

module Algebra.Properties.Monoid.Divisibility
  {a ℓ} (M : Monoid a ℓ) where

open Monoid M

------------------------------------------------------------------------
-- Re-export semigroup divisibility

open import Algebra.Properties.Semigroup.Divisibility semigroup public

------------------------------------------------------------------------
-- Additional properties

ε∣_ : ∀ x → ε ∣ x
ε∣ x = x , identityʳ x

∣-refl : Reflexive _∣_
∣-refl {x} = ε , identityˡ x

∣-reflexive : _≈_ ⇒ _∣_
∣-reflexive x≈y = ε , trans (identityˡ _) x≈y

∣-isPreorder : IsPreorder _≈_ _∣_
∣-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ∣-reflexive
  ; trans         = ∣-trans
  }

∣-preorder : Preorder a ℓ _
∣-preorder = record
  { isPreorder = ∣-isPreorder
  }

------------------------------------------------------------------------
-- Properties of mutual divisibiity

∣∣-refl : Reflexive _∣∣_
∣∣-refl = ∣-refl , ∣-refl

∣∣-reflexive : _≈_ ⇒ _∣∣_
∣∣-reflexive x≈y = ∣-reflexive x≈y , ∣-reflexive (sym x≈y)

∣∣-isEquivalence : IsEquivalence _∣∣_
∣∣-isEquivalence = record
  { refl  = λ {x} → ∣∣-refl {x}
  ; sym   = λ {x} {y} → ∣∣-sym {x} {y}
  ; trans = λ {x} {y} {z} → ∣∣-trans {x} {y} {z}
  }
