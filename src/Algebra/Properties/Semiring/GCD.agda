------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the Greatest Common Divisor over semirings.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Semiring)
open import Data.Product using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

module Algebra.Properties.Semiring.GCD {a ℓ} (R : Semiring a ℓ) where

open Semiring R
open import Algebra.Properties.Semiring.Primality R using (Coprime)
open import Algebra.Properties.Semiring.Divisibility R

------------------------------------------------------------------------
-- Re-exporting definition of GCD

open import Algebra.Definitions.RawSemiring rawSemiring public
  using (IsGCD; mkIsGCD)

------------------------------------------------------------------------
-- Properties of GCD

isGCD[0,x,x] : ∀ x → IsGCD 0# x x
isGCD[0,x,x] x = mkIsGCD (_∣0 x) ∣-refl (λ _ y∣x → y∣x)

isGCD[x,0,x] : ∀ x → IsGCD x 0# x
isGCD[x,0,x] x = mkIsGCD ∣-refl (_∣0 x) (λ y∣x _ → y∣x)

x≈0∧y≈0⇒gcd≈0 : ∀ {x y d} → IsGCD x y d → x ≈ 0# → y ≈ 0# → d ≈ 0#
x≈0∧y≈0⇒gcd≈0 (mkIsGCD _ _ greatest) x≈0 y≈0 = 0∣x⇒x≈0 (greatest
  (∣-respʳ (sym x≈0) (0# ∣0))
  (∣-respʳ (sym y≈0) (0# ∣0)))

x≉0∨y≉0⇒gcd≉0 : ∀ {x y d} → IsGCD x y d → x ≉ 0# ⊎ y ≉ 0# → d ≉ 0#
x≉0∨y≉0⇒gcd≉0 (mkIsGCD d∣x _ _) (inj₁ x≉0) = x∣y∧y≉0⇒x≉0 d∣x x≉0
x≉0∨y≉0⇒gcd≉0 (mkIsGCD _ d∣y _) (inj₂ y≉0) = x∣y∧y≉0⇒x≉0 d∣y y≉0

coprime⇒gcd∣1 : ∀ {x y d} → Coprime x y → IsGCD x y d →  d ∣ 1#
coprime⇒gcd∣1 coprime (mkIsGCD div₁ div₂ _) = coprime div₁ div₂

------------------------------------------------------------------------------
-- gcd-s for two division-equivalent pairs
-- are division-equivalent

GCD-unique : ∀ {x x' y y' d d'} → x ∣∣ x' → y ∣∣ y' →
             IsGCD x y d → IsGCD x' y' d' → d ∣∣ d'
GCD-unique (x∣x' , x'∣x) (y∣y' , y'∣y)
           (mkIsGCD d∣x d∣y greatest) (mkIsGCD d'∣x' d'∣y' greatest') = d∣d' , d'∣d
  where
  d∣x' = ∣-trans d∣x x∣x';    d∣y' = ∣-trans d∣y y∣y';    d∣d' = greatest' d∣x' d∣y'
  d'∣x = ∣-trans d'∣x' x'∣x;  d'∣y = ∣-trans d'∣y' y'∣y;  d'∣d = greatest d'∣x d'∣y
