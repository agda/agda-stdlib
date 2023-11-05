------------------------------------------------------------------------
-- The Agda standard library
--
-- Proof that the rationals form a HeytingField.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Properties.Heyting where

open import Data.Rational using (ℚ; ≢-nonZero; 1/_)
open import Data.Rational.Properties
  using (≡-decSetoid; +-*-commutativeRing; *-inverseˡ; *-inverseʳ)
open import Relation.Binary.Bundles using (DecSetoid)

open import Relation.Binary.Properties.DecSetoid ≡-decSetoid

open import Algebra.Apartness.Structures
open import Algebra using (CommutativeRing; Invertible)

open CommutativeRing +-*-commutativeRing hiding (_≉_)

-- some useful lemmas -- reproduced elsewhere?
private
  x-y≈0→x≈y : (x y : ℚ) → (x - y) ≈ 0# → x ≈ y
  x-y≈0→x≈y x y x-y≈0 =
    begin
      x
    ≈⟨ inverseˡ-unique x (- y) x-y≈0 ⟩
      - (- y)
    ≈⟨ ⁻¹-involutive y ⟩
      y
    ∎
    where
      open import Relation.Binary.Reasoning.Setoid setoid
      open import Algebra.Properties.Group +-group

  x≈y→x-y≈0 : (x y : ℚ) → x ≈ y → (x - y) ≈ 0#
  x≈y→x-y≈0 x y x≈y =
    begin
      x - y
    ≈⟨ +-congʳ x≈y ⟩
      y - y
    ≈⟨ -‿inverseʳ y ⟩
      0#
    ∎
    where
      open import Relation.Binary.Reasoning.Setoid setoid
      open import Algebra.Properties.Group +-group

  x≉y→x-y≉0 : (x y : ℚ) → x ≉ y → (x - y) ≉ 0#
  x≉y→x-y≉0 x y x≉y x-y≈0 = x≉y (x-y≈0→x≈y x y x-y≈0)

  x*y≈z→x≉0 : ∀ x y z → z ≉ 0# → x * y ≈ z → x ≉ 0#
  x*y≈z→x≉0 x y z z≉0 x*y≈z x≈0 =
    z≉0
    $ begin
        z
      ≈⟨ sym x*y≈z ⟩
        x * y
      ≈⟨ *-congʳ x≈0 ⟩
        0# * y
      ≈⟨ zeroˡ y ⟩
        0#
      ∎
    where
      open import Function using (_$_)
      open import Relation.Binary.Reasoning.Setoid setoid


  1≉0 : 1# ≉ 0#
  1≉0 = λ ()

isHeytingCommutativeRing : IsHeytingCommutativeRing _≈_ _≉_ _+_ _*_ -_ 0# 1#
isHeytingCommutativeRing =
  record
  { isCommutativeRing = isCommutativeRing
  ; isApartnessRelation = ≉-isApartnessRelation
  ; #⇒invertible =
    λ {x} {y} x≉y →
      let nz = ≢-nonZero (x≉y→x-y≉0 x y x≉y)
      in
        ( 1/_ (x - y) {{nz}}
        , *-inverseˡ (x - y) {{nz}} , *-inverseʳ (x - y) {{nz}}
        )
  ; invertible⇒# = invert→#
  }
  where
    open import Data.Product using (_,_)

    invert→# : ∀ {x y} → Invertible _≈_ 1# _*_ (x - y) → x ≉ y
    invert→# {x} {y} (1/[x-y] , _ , [x-y]/[x-y]≈1) x≈y =
      x*y≈z→x≉0 (x - y) 1/[x-y] 1# 1≉0 [x-y]/[x-y]≈1 (x≈y→x-y≈0 x y x≈y)

isHeytingField : IsHeytingField _≈_ _≉_ _+_ _*_ -_ 0# 1#
isHeytingField =
  record
  { isHeytingCommutativeRing = isHeytingCommutativeRing
  ; tight = ≉-tight
  }
