------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of divisibility
------------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.(Magma/Semigroup/...).Divisibility`

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Data.Product using (∃; _×_; _,_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (¬_)

module Algebra.Divisibility
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A)
  where

open import Algebra.Definitions _≈_

------------------------------------------------------------------------
-- Definitions

-- Divisibility

infix 5 _∣_ _∤_ _∣∣_ _¬∣∣_

_∣_ : Rel A (a ⊔ ℓ)
x ∣ y = ∃ λ q → (q ∙ x) ≈ y

_∤_ : Rel A (a ⊔ ℓ)
x ∤ y = ¬ x ∣ y

-- Mutual divisibility.

-- When in a cancellative monoid, elements related by _∣∣_ are called
-- associated and if x ∣∣ y then x and y differ by an invertible factor.

_∣∣_ : Rel A (a ⊔ ℓ)
x ∣∣ y = x ∣ y × y ∣ x

_¬∣∣_ : Rel A (a ⊔ ℓ)
x ¬∣∣ y =  ¬ x ∣∣ y

------------------------------------------------------------------------
-- Properties

∣-refl : ∀ {ε} → LeftIdentity ε _∙_ → Reflexive _∣_
∣-refl {ε} idˡ {x} = ε , idˡ x

∣-reflexive : Transitive _≈_ → ∀ {ε} → LeftIdentity ε _∙_ → _≈_ ⇒ _∣_
∣-reflexive trans {ε} idˡ x≈y = ε , trans (idˡ _) x≈y

∣-trans : Transitive _≈_ → LeftCongruent _∙_ → Associative _∙_ → Transitive _∣_
∣-trans trans congˡ assoc {x} {y} {z} (p , px≈y) (q , qy≈z) =
  q ∙ p , trans (assoc q p x) (trans (congˡ px≈y) qy≈z)

∣-respʳ : Transitive _≈_ → _∣_ Respectsʳ _≈_
∣-respʳ trans y≈z (q , qx≈y) = q , trans qx≈y y≈z

∣-respˡ : Symmetric _≈_ → Transitive _≈_ → LeftCongruent _∙_ → _∣_ Respectsˡ _≈_
∣-respˡ sym trans congˡ x≈z (q , qx≈y) = q , trans (congˡ (sym x≈z)) qx≈y

∣-resp : Symmetric _≈_ → Transitive _≈_ → LeftCongruent _∙_ → _∣_ Respects₂ _≈_
∣-resp sym trans cong = ∣-respʳ trans , ∣-respˡ sym trans cong

∣-min : ∀ {ε} → RightIdentity ε _∙_ → Minimum _∣_ ε
∣-min {ε} idʳ x = x , idʳ x

∣-max : ∀ {ε} → LeftZero ε _∙_ → Maximum _∣_ ε
∣-max {ε} zeˡ x = ε , zeˡ x
