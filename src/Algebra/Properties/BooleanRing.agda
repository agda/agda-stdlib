------------------------------------------------------------------------
-- The Agda standard library
--
-- Some basic properties of Rings
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles
  using (BooleanRing; CommutativeMonoid; IdempotentCommutativeMonoid; CommutativeRing)

module Algebra.Properties.BooleanRing {r₁ r₂} (R : BooleanRing r₁ r₂) where

open import Function.Base using (_∘_; _$_)

open BooleanRing R
open import Algebra.Definitions _≈_
open import Algebra.Structures _≈_
  using (IsCommutativeMonoid; IsIdempotentCommutativeMonoid; IsCommutativeRing)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- Export properties of rings

open import Algebra.Properties.Ring ring public

------------------------------------------------------------------------
-- Extra properties of Boolean rings

xy+yx≈0 : ∀ x y → x * y + y * x ≈ 0#
xy+yx≈0 x y = +-cancelˡ (x * x) _ _ $ +-cancelʳ (y * y) _ _ $ begin
  x * x + ((x * y) + (y * x)) + y * y ≈⟨ +-congʳ (+-assoc _ _ _) ⟨
  x * x + x * y + y * x + y * y       ≈⟨ +-assoc _ _ _ ⟩
  (x * x + x * y) + (y * x + y * y)   ≈⟨ +-cong (distribˡ x x y) (distribˡ y x y) ⟨
  x * (x + y) + y * (x + y)           ≈⟨ distribʳ (x + y) x y ⟨
  (x + y) * (x + y)                   ≈⟨ *-idem (x + y) ⟩
  x + y                               ≈⟨ +-congˡ (*-idem y) ⟨
  x + y * y                           ≈⟨ +-congʳ (*-idem x) ⟨
  x * x + y * y                       ≈⟨ +-congʳ (+-identityʳ (x * x)) ⟨
  x * x + 0# + y * y                  ∎

y≈x⇒x+y≈0 : ∀ {x y} → y ≈ x → x + y ≈ 0#
y≈x⇒x+y≈0 {x = x} {y = y} y≈x = begin
  x + y         ≈⟨ +-cong (*-idem x) (*-idem y) ⟨
  x * x + y * y ≈⟨ +-cong (*-congˡ (sym y≈x)) (*-congˡ y≈x) ⟩
  x * y + y * x ≈⟨ xy+yx≈0 x y ⟩
  0#            ∎

x+x≈0 : ∀ x → x + x ≈ 0#
x+x≈0 x = y≈x⇒x+y≈0 refl

x+y≈0⇒y≈x : ∀ {x y} → x + y ≈ 0# → y ≈ x
x+y≈0⇒y≈x {x = x} {y = y} x+y≈0 = begin
  y   ≈⟨ +-inverseʳ-unique x y x+y≈0 ⟩
  - x ≈⟨ +-inverseˡ-unique x x (x+x≈0 x) ⟨
  x   ∎

-x≈x : ∀ x → - x ≈ x
-x≈x = x+y≈0⇒y≈x ∘ -‿inverseʳ

*-comm : Commutative _*_
*-comm x y = begin
  x * y     ≈⟨ +-inverseˡ-unique  _ _ (xy+yx≈0 x y) ⟩
  - (y * x) ≈⟨ -x≈x _ ⟩
  y * x     ∎

------------------------------------------------------------------------
-- Additional structures

*-isCommutativeMonoid : IsCommutativeMonoid _*_ 1#
*-isCommutativeMonoid = record { isMonoid = *-isMonoid ; comm = *-comm }

*-isIdempotentCommutativeMonoid : IsIdempotentCommutativeMonoid _*_ 1#
*-isIdempotentCommutativeMonoid = record
  { isCommutativeMonoid = *-isCommutativeMonoid
  ; idem = *-idem
  }

isCommutativeRing : IsCommutativeRing _+_ _*_ -_ 0# 1#
isCommutativeRing = record { isRing = isRing ; *-comm = *-comm }

------------------------------------------------------------------------
-- Additional bundles

*-commutativeMonoid : CommutativeMonoid _ _
*-commutativeMonoid = record { isCommutativeMonoid = *-isCommutativeMonoid }

*-idempotentCommutativeMonoid : IdempotentCommutativeMonoid _ _
*-idempotentCommutativeMonoid = record
  { isIdempotentCommutativeMonoid = *-isIdempotentCommutativeMonoid }

commutativeRing : CommutativeRing _ _
commutativeRing = record { isCommutativeRing = isCommutativeRing }
