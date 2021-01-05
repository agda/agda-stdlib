-----------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of divisibility
-----------------------------------------------------------------------

-- You're unlikely to want to use this module directly. Instead you
-- probably want to be importing the appropriate module from
-- `Algebra.Properties.(Magma/Semigroup/...).Divisibility`

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; swap)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Nullary using (¬_)

module Algebra.Divisibility
  {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) (_∙_ : Op₂ A)
  where

open import Algebra.Definitions _≈_

-----------------------------------------------------------------------
-- Divisibility

infix 5 _∣ˡ_ _∤ˡ_ _∣ʳ_ _∤ʳ_ _∣_ _∤_

-- Divisibility from the left

_∣ˡ_ : Rel A (a ⊔ ℓ)
x ∣ˡ y = ∃ λ q → (x ∙ q) ≈ y

_∤ˡ_ : Rel A (a ⊔ ℓ)
x ∤ˡ y = ¬ x ∣ˡ y

-- Divisibility from the right

_∣ʳ_ : Rel A (a ⊔ ℓ)
x ∣ʳ y = ∃ λ q → (q ∙ x) ≈ y

_∤ʳ_ : Rel A (a ⊔ ℓ)
x ∤ʳ y = ¬ x ∣ʳ y

-- _∣ˡ_ and _∣ʳ_ are only equivalent in the commutative case. In this
-- case we take the right definition to be the primary one.

_∣_ : Rel A (a ⊔ ℓ)
_∣_ = _∣ʳ_

_∤_ : Rel A (a ⊔ ℓ)
x ∤ y = ¬ x ∣ y

------------------------------------------------------------------------
-- Mutual divisibility _∣∣_.
-- In a  monoid,  this is an equivalence relation extending _≈_.
-- When in a  cancellative monoid,  elements related by _∣∣_ are called
-- associated,  and there x ∣∣ y is equivalent to that x and y differ by
-- some invertible factor.
-- Example: for ℕ  this is equivalent to  x ≡ y,
--          for ℤ  this is equivalent to  (x ≡ y  or  x ≡ -y).

_∣∣_ : Rel A (a ⊔ ℓ)
x ∣∣ y = x ∣ y × y ∣ x

_∤∤_ : Rel A (a ⊔ ℓ)
x ∤∤ y =  ¬ x ∣∣ y

------------------------------------------------------------------------------
-- Greatest common divisor (GCD)

record IsGCD (x y gcd : A) : Set (a ⊔ ℓ) where
  constructor isGCDᶜ
  field
    divides₁ : gcd ∣ x
    divides₂ : gcd ∣ y
    greatest : ∀ {z} → z ∣ x → z ∣ y → z ∣ gcd

  quot₁ : A               -- a complementory quotient  x/gcd
  quot₁ = proj₁ divides₁

  quot₂ : A               -- y/gcd
  quot₂ = proj₁ divides₂

  quot₁∙gcd≈x : (quot₁ ∙ gcd) ≈ x
  quot₁∙gcd≈x = proj₂ divides₁

  quot₂∙gcd≈y : (quot₂ ∙ gcd) ≈ y
  quot₂∙gcd≈y = proj₂ divides₂


------------------------------------------------------------------------
-- Properties of _∣_ and _∣∣_

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

∣∣-refl : ∀ {ε} → LeftIdentity ε _∙_ → Reflexive _∣∣_
∣∣-refl idˡ = ∣-refl idˡ , ∣-refl idˡ

∣∣-reflexive : Symmetric _≈_ → Transitive _≈_ → ∀ {ε} → LeftIdentity ε _∙_ →
  _≈_ ⇒ _∣∣_
∣∣-reflexive sym trans idˡ x≈y = ∣-reflexive trans idˡ x≈y , ∣-reflexive trans idˡ (sym x≈y)

∣∣-sym : Symmetric _∣∣_
∣∣-sym = swap

∣∣-trans : Transitive _≈_ → LeftCongruent _∙_ → Associative _∙_ → Transitive _∣∣_
∣∣-trans trans congˡ assoc {x} {y} {z} (x∣y , y∣x) (y∣z , z∣y) =
  ∣-trans trans congˡ assoc x∣y y∣z , ∣-trans trans congˡ assoc z∣y y∣x

∣∣-respʳ : Symmetric _≈_ → Transitive _≈_ → LeftCongruent _∙_ → _∣∣_ Respectsʳ _≈_
∣∣-respʳ sym trans congˡ y≈z (x∣y , y∣x) =
  ∣-respʳ trans y≈z x∣y , ∣-respˡ sym trans congˡ y≈z y∣x

∣∣-respˡ : Symmetric _≈_ → Transitive _≈_ → LeftCongruent _∙_ → _∣∣_ Respectsˡ _≈_
∣∣-respˡ sym trans congˡ x≈z (x∣y , y∣x) =
  ∣-respˡ sym trans congˡ x≈z x∣y , ∣-respʳ trans x≈z y∣x

∣∣-resp : Symmetric _≈_ → Transitive _≈_ → LeftCongruent _∙_ → _∣∣_ Respects₂ _≈_
∣∣-resp sym trans cong = ∣∣-respʳ sym trans cong , ∣∣-respˡ sym trans cong
