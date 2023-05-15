------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Heyting Commutative Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Apartness.Bundles using (HeytingCommutativeRing)

module Algebra.Apartness.Properties.HeytingCommutativeRing
  {c ℓ₁ ℓ₂} (HCR : HeytingCommutativeRing c ℓ₁ ℓ₂) where

open import Function using (_∘_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Algebra using (CommutativeRing; RightIdentity; Invertible; LeftInvertible; RightInvertible)

open HeytingCommutativeRing HCR
open CommutativeRing commutativeRing using (ring)

open import Algebra.Properties.Ring ring
  using (-0#≈0#; -‿distribˡ-*; -‿distribʳ-*; -‿anti-homo-+; -‿involutive)
open import Relation.Binary.Definitions using (Symmetric)
import Relation.Binary.Reasoning.Setoid as ReasonSetoid

private variable
  x y z : Carrier

leftInv→rightInv : LeftInvertible _≈_ 1# _*_ x → RightInvertible _≈_ 1# _*_ x
leftInv→rightInv {x} (x⁻¹ , x⁻¹*x≈1) = x⁻¹ , trans (*-comm x x⁻¹) x⁻¹*x≈1

rightInv→leftInv : RightInvertible _≈_ 1# _*_ x → LeftInvertible _≈_ 1# _*_ x
rightInv→leftInv {x} (x⁻¹ , x*x⁻¹≈1) = x⁻¹ , trans (*-comm x⁻¹ x) x*x⁻¹≈1

leftInv→Inv : LeftInvertible _≈_ 1# _*_ (x - y) → Invertible _≈_ 1# _*_ (x - y)
leftInv→Inv left@(x⁻¹ , x⁻¹*x≈1) = x⁻¹ , x⁻¹*x≈1 , leftInv→rightInv left .proj₂

rightInv→Inv : RightInvertible _≈_ 1# _*_ (x - y) → Invertible _≈_ 1# _*_ (x - y)
rightInv→Inv right@(x⁻¹ , x*x⁻¹≈1) = x⁻¹ , rightInv→leftInv right .proj₂ , x*x⁻¹≈1

leftInvertible⇒# : LeftInvertible _≈_ 1# _*_ (x - y) → x # y
leftInvertible⇒# = invertible⇒# ∘ leftInv→Inv

rightInvertible⇒# : RightInvertible _≈_ 1# _*_ (x - y) → x # y
rightInvertible⇒# = invertible⇒# ∘ rightInv→Inv

x-0≈x : RightIdentity _≈_ 0# _-_
x-0≈x x = trans (+-congˡ -0#≈0#) (+-identityʳ x)

1#0 : 1# # 0#
1#0 = leftInvertible⇒# (1# , 1*[x-0]≈x)
  where
  1*[x-0]≈x : 1# * (x - 0#) ≈ x
  1*[x-0]≈x {x} = trans (*-identityˡ (x - 0#)) (x-0≈x x)

x#0y#0→xy#0 : x # 0# → y # 0# → x * y # 0#
x#0y#0→xy#0 {x} {y} x#0 y#0 = leftInvertible⇒# (y⁻¹ * x⁻¹ , y⁻¹*x⁻¹*x*y≈1)
  where
  open ReasonSetoid setoid

  InvX : Invertible _≈_ 1# _*_ (x - 0#)
  InvX = #⇒invertible x#0

  x⁻¹ = InvX .proj₁

  x⁻¹*x≈1 : x⁻¹ * (x - 0#) ≈ 1#
  x⁻¹*x≈1 = InvX .proj₂ .proj₁

  x*x⁻¹≈1 : (x - 0#) * x⁻¹ ≈ 1#
  x*x⁻¹≈1 = InvX .proj₂ .proj₂

  InvY : Invertible _≈_ 1# _*_ (y - 0#)
  InvY = #⇒invertible y#0

  y⁻¹ = InvY .proj₁

  y⁻¹*y≈1 : y⁻¹ * (y - 0#) ≈ 1#
  y⁻¹*y≈1 = InvY .proj₂ .proj₁

  y*y⁻¹≈1 : (y - 0#) * y⁻¹ ≈ 1#
  y*y⁻¹≈1 = InvY .proj₂ .proj₂

  y⁻¹*x⁻¹*x*y≈1 : y⁻¹ * x⁻¹ * (x * y - 0#) ≈ 1#
  y⁻¹*x⁻¹*x*y≈1 = begin
    y⁻¹ * x⁻¹ * (x * y - 0#)     ≈⟨ *-congˡ (x-0≈x (x * y)) ⟩
    y⁻¹ * x⁻¹ * (x * y)          ≈⟨ *-assoc y⁻¹ x⁻¹ (x * y) ⟩
    y⁻¹ * (x⁻¹ * (x * y))       ≈˘⟨ *-congˡ (*-assoc x⁻¹ x y) ⟩
    y⁻¹ * ((x⁻¹ * x) * y)       ≈˘⟨ *-congˡ (*-congʳ (*-congˡ (x-0≈x x))) ⟩
    y⁻¹ * ((x⁻¹ * (x - 0#)) * y) ≈⟨ *-congˡ (*-congʳ x⁻¹*x≈1) ⟩
    y⁻¹ * (1# * y)               ≈⟨ *-congˡ (*-identityˡ y) ⟩
    y⁻¹ * y                     ≈˘⟨ *-congˡ (x-0≈x y) ⟩
    y⁻¹ * (y - 0#)               ≈⟨ y⁻¹*y≈1 ⟩
    1# ∎


#-sym : Symmetric _#_
#-sym {x} {y} x#y = leftInvertible⇒# (- x-y⁻¹ , x-y⁻¹*y-x≈1)
  where
  open ReasonSetoid setoid
  InvX-Y : Invertible _≈_ 1# _*_ (x - y)
  InvX-Y = #⇒invertible x#y

  x-y⁻¹ = InvX-Y .proj₁

  y-x≈-[x-y] : y - x ≈ - (x - y)
  y-x≈-[x-y] = begin
    y - x     ≈˘⟨ +-congʳ (-‿involutive y) ⟩
    - - y - x ≈˘⟨ -‿anti-homo-+ x (- y) ⟩
    - (x - y) ∎

  x-y⁻¹*y-x≈1 : (- x-y⁻¹) * (y - x) ≈ 1#
  x-y⁻¹*y-x≈1 = begin
    (- x-y⁻¹) * (y - x)   ≈˘⟨ -‿distribˡ-* x-y⁻¹ (y - x) ⟩
    - (x-y⁻¹ * (y - x))    ≈⟨ -‿cong (*-congˡ y-x≈-[x-y]) ⟩
    - (x-y⁻¹ * - (x - y)) ≈˘⟨ -‿cong (-‿distribʳ-* x-y⁻¹ (x - y)) ⟩
    - - (x-y⁻¹ * (x - y))  ≈⟨ -‿involutive (x-y⁻¹ * ((x - y))) ⟩
    x-y⁻¹ * (x - y)        ≈⟨ InvX-Y .proj₂ .proj₁ ⟩
    1# ∎


#-congʳ : x ≈ y → x # z → y # z
#-congʳ {x} {y} {z} x≈y x#z = leftInvertible⇒# (x-z⁻¹ , x-z⁻¹*y-z≈1)
  where
  open ReasonSetoid setoid

  InvXZ : Invertible _≈_ 1# _*_ (x - z)
  InvXZ = #⇒invertible x#z

  x-z⁻¹ = InvXZ .proj₁

  x-z⁻¹*x-z≈1# : x-z⁻¹ * (x - z) ≈ 1#
  x-z⁻¹*x-z≈1# = InvXZ .proj₂ .proj₁

  x-z*x-z⁻¹≈1# : (x - z) * x-z⁻¹ ≈ 1#
  x-z*x-z⁻¹≈1# = InvXZ .proj₂ .proj₂

  x-z⁻¹*y-z≈1 : x-z⁻¹ * (y - z) ≈ 1#
  x-z⁻¹*y-z≈1 = begin
    x-z⁻¹ * (y - z) ≈˘⟨ *-congˡ (+-congʳ x≈y) ⟩
    x-z⁻¹ * (x - z)  ≈⟨ x-z⁻¹*x-z≈1# ⟩
    1# ∎

#-congˡ : y ≈ z → x # y → x # z
#-congˡ y≈z x#y = #-sym (#-congʳ y≈z (#-sym x#y))
