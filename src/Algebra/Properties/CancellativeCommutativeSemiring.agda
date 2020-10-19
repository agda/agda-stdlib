------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for CancellativeCommutativeSemiring.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Magma; CommutativeSemiring; CancellativeCommutativeSemiring)
import Algebra.Properties.Semigroup
import Algebra.Properties.Semiring
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; case_of_; flip)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; Symmetric; Setoid)
open import Relation.Unary using (Pred)

module Algebra.Properties.CancellativeCommutativeSemiring {α ℓ}
       (R : CancellativeCommutativeSemiring α ℓ)
       (open CancellativeCommutativeSemiring R)
       (open Setoid setoid using (_≉_))
       (0≉1 : 0# ≉ 1#)
       where

open CommutativeSemiring +-*-commutativeSemiring using (*-magma; *-semigroup; semiring)
open Algebra.Properties.Semigroup *-semigroup using (_∣_; _∤_; ∣-trans; bothFactors-∣≈)
open Algebra.Properties.Semiring semiring using (∣nonzero⇒≉0)

private C = Carrier

1≉0 : 1# ≉ 0#
1≉0 = 0≉1 ∘ sym

0∤1 : 0# ∤ 1#
0∤1 (q , 1≈q*0) = 1≉0 (trans 1≈q*0 (zeroʳ q))

------------------------------------------------------------------------------
-- Irreducibilty and its properties.
------------------------------------------------------------------------------

IsIrreducible : Pred C (α ⊔ ℓ)
IsIrreducible p =  p ∤ 1#  ×  (∀ {x y} → (p ≈ x * y) → x ∣ 1# ⊎ y ∣ 1#)

IsPrime :  Pred C (α ⊔ ℓ)
IsPrime p =  p ≉ 0#  ×  p ∤ 1#  ×  ∀ {x y} → p ∣ (x * y) → p ∣ x ⊎ p ∣ y

-- In a GCDDomain,  IsIrreducible is equivalent to IsPrime.

irreducible≉0 :  ∀ {p} → IsIrreducible p → p ≉ 0#
irreducible≉0 (_ , chooseInvertible) p≈0 =
  let p≈0*0 = trans p≈0 (sym (zeroˡ 0#)) in
  case chooseInvertible p≈0*0 of \
  { (inj₁ 0∣1) → 0∤1 0∣1
  ; (inj₂ 0∣1) → 0∤1 0∣1
  }

Coprime : Rel C (α ⊔ ℓ)
Coprime a b = ∀ {c} → c ∣ a → c ∣ b → c ∣ 1#

Coprime-sym : Symmetric Coprime
Coprime-sym coprime = flip coprime

coprimeWithInvertible : ∀ {x} y → x ∣ 1# → Coprime x y
coprimeWithInvertible {x} y x∣1 z∣x _ = ∣-trans z∣x x∣1

------------------------------------------------------------------------------
-- Greatest common divisor (GCD) notion and its properties.
------------------------------------------------------------------------------

record GCD (a b : C) :  Set (α ⊔ ℓ) where      -- a result of gcd
  constructor gcdᶜ
  field
    proper   : C                 -- the proper gcd value
    divides₁ : proper ∣ a
    divides₂ : proper ∣ b
    greatest : ∀ {d} → (d ∣ a) → (d ∣ b) → (d ∣ proper)

  ----------------------------------------------------------------------------
  -- Several properties proved in-place

  quot₁ quot₂ : C
  quot₁ = proj₁ divides₁
  quot₂ = proj₁ divides₂

  a≈quot₁*proper :  a ≈ quot₁ * proper
  a≈quot₁*proper =  proj₂ divides₁

  b≈quot₂*proper :  b ≈ quot₂ * proper
  b≈quot₂*proper =  proj₂ divides₂

  quot₁∣a :  quot₁ ∣ a
  quot₁∣a =  proj₂ (bothFactors-∣≈ *-comm proper quot₁ a a≈quot₁*proper)

  quot₂∣b :  quot₂ ∣ b
  quot₂∣b =  proj₂ (bothFactors-∣≈ *-comm proper quot₂ b b≈quot₂*proper)

