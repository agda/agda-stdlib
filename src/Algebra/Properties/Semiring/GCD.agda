------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the Greatest Common Divisor over semirings.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

module Algebra.Properties.Semiring.GCD {a ℓ} (R : Semiring a ℓ) where

open Semiring R
open import Algebra.Properties.Semiring.Primality R using (Coprime)
open import Algebra.Properties.Semiring.Divisibility R

------------------------------------------------------------------------
-- Re-exporting definition of GCD

open import Algebra.Definitions.RawSemiring rawSemiring public
  using (IsGCD; isGCDᶜ)

------------------------------------------------------------------------
-- Properties of GCD

isGCD[0,x,x] : ∀ x → IsGCD 0# x x
isGCD[0,x,x] x = isGCDᶜ (_∣0 x) ∣-refl (λ _ y∣x → y∣x)

isGCD[x,0,x] : ∀ x → IsGCD x 0# x
isGCD[x,0,x] x = isGCDᶜ ∣-refl (_∣0 x) (λ y∣x _ → y∣x)

x≈0∧y≈0⇒gcd≈0 : ∀ {x y d} → IsGCD x y d → x ≈ 0# → y ≈ 0# → d ≈ 0#
x≈0∧y≈0⇒gcd≈0 (isGCDᶜ _ _ greatest) x≈0 y≈0 = 0∣x⇒x≈0 (greatest
  (∣-respʳ (sym x≈0) (0# ∣0))
  (∣-respʳ (sym y≈0) (0# ∣0)))

x≉0∨y≉0⇒gcd≉0 : ∀ {x y d} → IsGCD x y d → x ≉ 0# ⊎ y ≉ 0# → d ≉ 0#
x≉0∨y≉0⇒gcd≉0 (isGCDᶜ d∣x _ _) (inj₁ x≉0) = x∣y∧y≉0⇒x≉0 d∣x x≉0
x≉0∨y≉0⇒gcd≉0 (isGCDᶜ _ d∣y _) (inj₂ y≉0) = x∣y∧y≉0⇒x≉0 d∣y y≉0

coprime⇒gcd∣1 : ∀ {x y d} → Coprime x y → IsGCD x y d →  d ∣ 1#
coprime⇒gcd∣1 coprime (isGCDᶜ div₁ div₂ _) = coprime div₁ div₂
