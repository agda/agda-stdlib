------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Heyting Fields
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Apartness.Bundles using (HeytingField)

module Algebra.Apartness.Properties.HeytingField
  {c ℓ₁ ℓ₂} (HF : HeytingField c ℓ₁ ℓ₂) where

open import Function.Base using (_∘_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Algebra.Bundles using (CommutativeRing)

open HeytingField HF
open CommutativeRing commutativeRing using (ring; *-commutativeMonoid)

open import Algebra.Definitions _≈_
  using (Invertible; LeftInvertible; RightInvertible)
open import Algebra.Properties.CommutativeMonoid *-commutativeMonoid
  using (invertibleˡ⇒invertible; invertibleʳ⇒invertible)
open import Algebra.Properties.Ring ring
  using (x-0#≈x; -‿distribˡ-*; -‿distribʳ-*; -‿anti-homo-+; -‿involutive)
open import Relation.Binary.Definitions using (Symmetric)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

private
  variable
    x y z : Carrier


invertibleˡ⇒# : LeftInvertible 1# _*_ (x - y) → x # y
invertibleˡ⇒# = invertible⇒# ∘ invertibleˡ⇒invertible

invertibleʳ⇒# : RightInvertible 1# _*_ (x - y) → x # y
invertibleʳ⇒# = invertible⇒# ∘ invertibleʳ⇒invertible

1#0 : 1# # 0#
1#0 = invertibleˡ⇒# (1# , 1*[x-0]≈x)
  where
  1*[x-0]≈x : 1# * (x - 0#) ≈ x
  1*[x-0]≈x {x} = trans (*-identityˡ (x - 0#)) (x-0#≈x x)

x#0y#0→xy#0 : x # 0# → y # 0# → x * y # 0#
x#0y#0→xy#0 {x} {y} x#0 y#0 = helper (#⇒invertible x#0) (#⇒invertible y#0)
  where
  open ≈-Reasoning setoid

  helper : Invertible 1# _*_ (x - 0#) → Invertible 1# _*_ (y - 0#) → x * y # 0#
  helper (x⁻¹ , x⁻¹*x≈1 , x*x⁻¹≈1) (y⁻¹ , y⁻¹*y≈1 , y*y⁻¹≈1)
    = invertibleˡ⇒# (y⁻¹ * x⁻¹ , y⁻¹*x⁻¹*x*y≈1)
    where

    y⁻¹*x⁻¹*x*y≈1 : y⁻¹ * x⁻¹ * (x * y - 0#) ≈ 1#
    y⁻¹*x⁻¹*x*y≈1 = begin
      y⁻¹ * x⁻¹ * (x * y - 0#)     ≈⟨ *-congˡ (x-0#≈x (x * y)) ⟩
      y⁻¹ * x⁻¹ * (x * y)          ≈⟨ *-assoc y⁻¹ x⁻¹ (x * y) ⟩
      y⁻¹ * (x⁻¹ * (x * y))        ≈⟨ *-congˡ (*-assoc x⁻¹ x y) ⟨
      y⁻¹ * ((x⁻¹ * x) * y)        ≈⟨ *-congˡ (*-congʳ (*-congˡ (x-0#≈x x))) ⟨
      y⁻¹ * ((x⁻¹ * (x - 0#)) * y) ≈⟨ *-congˡ (*-congʳ x⁻¹*x≈1) ⟩
      y⁻¹ * (1# * y)               ≈⟨ *-congˡ (*-identityˡ y) ⟩
      y⁻¹ * y                      ≈⟨ *-congˡ (x-0#≈x y) ⟨
      y⁻¹ * (y - 0#)               ≈⟨ y⁻¹*y≈1 ⟩
      1#                           ∎

#-sym : Symmetric _#_
#-sym {x} {y} x#y = invertibleˡ⇒# (- x-y⁻¹ , x-y⁻¹*y-x≈1)
  where
  open ≈-Reasoning setoid
  InvX-Y : Invertible 1# _*_ (x - y)
  InvX-Y = #⇒invertible x#y

  x-y⁻¹ = InvX-Y .proj₁

  y-x≈-[x-y] : y - x ≈ - (x - y)
  y-x≈-[x-y] = begin
    y - x     ≈⟨ +-congʳ (-‿involutive y) ⟨
    - - y - x ≈⟨ -‿anti-homo-+ x (- y) ⟨
    - (x - y) ∎

  x-y⁻¹*y-x≈1 : (- x-y⁻¹) * (y - x) ≈ 1#
  x-y⁻¹*y-x≈1 = begin
    (- x-y⁻¹) * (y - x)   ≈⟨ -‿distribˡ-* x-y⁻¹ (y - x) ⟨
    - (x-y⁻¹ * (y - x))   ≈⟨ -‿cong (*-congˡ y-x≈-[x-y]) ⟩
    - (x-y⁻¹ * - (x - y)) ≈⟨ -‿cong (-‿distribʳ-* x-y⁻¹ (x - y)) ⟨
    - - (x-y⁻¹ * (x - y)) ≈⟨ -‿involutive (x-y⁻¹ * (x - y)) ⟩
    x-y⁻¹ * (x - y)       ≈⟨ InvX-Y .proj₂ .proj₁ ⟩
    1#                    ∎

#-congʳ : x ≈ y → x # z → y # z
#-congʳ {x} {y} {z} x≈y = helper ∘ #⇒invertible
  where
  open ≈-Reasoning setoid

  helper : Invertible 1# _*_ (x - z) → y # z
  helper (x-z⁻¹ , x-z⁻¹*x-z≈1# , x-z*x-z⁻¹≈1#)
    = invertibleˡ⇒# (x-z⁻¹ , x-z⁻¹*y-z≈1)
    where
    x-z⁻¹*y-z≈1 : x-z⁻¹ * (y - z) ≈ 1#
    x-z⁻¹*y-z≈1 = begin
      x-z⁻¹ * (y - z) ≈⟨ *-congˡ (+-congʳ x≈y) ⟨
      x-z⁻¹ * (x - z) ≈⟨ x-z⁻¹*x-z≈1# ⟩
      1#              ∎

#-congˡ : y ≈ z → x # y → x # z
#-congˡ y≈z = #-sym ∘ #-congʳ y≈z ∘ #-sym
