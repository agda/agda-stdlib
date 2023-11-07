------------------------------------------------------------------------
-- The Agda standard library
--
-- Proof that the rationals form a HeytingField.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Rational.Properties.Heyting where

open import Level using (0ℓ)

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Data.Rational using (ℚ; ≢-nonZero; 1/_; 0ℚ; 1ℚ)
open import Data.Rational.Properties
  using
  ( ≡-decSetoid; +-*-commutativeRing; *-inverseˡ; *-inverseʳ; 1≢0 )

open import Relation.Binary.Properties.DecSetoid ≡-decSetoid

open import Algebra.Apartness
  using
  ( IsHeytingCommutativeRing; IsHeytingField
  ; HeytingCommutativeRing; HeytingField
  )

open import Algebra using (CommutativeRing; Invertible; Group)
open import Data.Product using (_,_)

private
  module _ {c ℓ} (G : Group c ℓ) where
    open Group G
    open import Algebra.Properties.Group G
    open import Relation.Binary.Reasoning.Setoid setoid

    x∙y⁻¹≈ε→x≈y : (x y : Carrier) → (x ∙ y ⁻¹) ≈ ε → x ≈ y
    x∙y⁻¹≈ε→x≈y x y x∙y⁻¹≈ε =
      begin
        x
      ≈⟨ inverseˡ-unique x (y ⁻¹) x∙y⁻¹≈ε ⟩
        (y ⁻¹) ⁻¹
      ≈⟨ ⁻¹-involutive y ⟩
        y
      ∎

    x≈y→x∙y⁻¹≈ε : (x y : Carrier) → x ≈ y → (x ∙ y ⁻¹) ≈ ε
    x≈y→x∙y⁻¹≈ε x y x≈y =
      begin
        x ∙ y ⁻¹
      ≈⟨ ∙-congʳ x≈y ⟩
        y ∙ y ⁻¹
      ≈⟨ inverseʳ y ⟩
        ε
      ∎

    x≉y→x∙y⁻¹≉ε : (x y : Carrier) → x ≉ y → (x ∙ y ⁻¹) ≉ ε
    x≉y→x∙y⁻¹≉ε x y x≉y x∙y⁻¹≈ε = x≉y (x∙y⁻¹≈ε→x≈y x y x∙y⁻¹≈ε)

  module _ {c ℓ} (R : CommutativeRing c ℓ) where
    open CommutativeRing R
    open import Relation.Binary.Reasoning.Setoid setoid

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


open CommutativeRing +-*-commutativeRing

isHeytingCommutativeRing : IsHeytingCommutativeRing _≡_ _≢_ _+_ _*_ -_ 0ℚ 1ℚ
isHeytingCommutativeRing =
  record
  { isCommutativeRing = isCommutativeRing
  ; isApartnessRelation = ≉-isApartnessRelation
  ; #⇒invertible = #⇒invertible
  ; invertible⇒# = invertible⇒#
  }
  where

    #⇒invertible : {x y : ℚ} → x ≢ y → Invertible _≡_ 1ℚ _*_ (x - y)
    #⇒invertible {x} {y} x≉y =
      ( 1/_ (x - y) ⦃ nz ⦄
      , *-inverseˡ (x - y) ⦃ nz ⦄ , *-inverseʳ (x - y) ⦃ nz ⦄
      )
      where nz = ≢-nonZero (x≉y→x∙y⁻¹≉ε +-group x y x≉y)

    invertible⇒# : ∀ {x y} → Invertible _≈_ 1# _*_ (x - y) → x ≉ y
    invertible⇒# {x} {y} (1/[x-y] , _ , [x-y]/[x-y]≈1) x≈y =
      x*y≈z→x≉0 +-*-commutativeRing (x - y) 1/[x-y] 1# 1≢0 [x-y]/[x-y]≈1 (x≈y→x∙y⁻¹≈ε +-group x y x≈y)

isHeytingField : IsHeytingField _≈_ _≉_ _+_ _*_ -_ 0# 1#
isHeytingField =
  record
  { isHeytingCommutativeRing = isHeytingCommutativeRing
  ; tight = ≉-tight
  }

heytingCommutativeRing : HeytingCommutativeRing 0ℓ 0ℓ 0ℓ
heytingCommutativeRing =
  record { isHeytingCommutativeRing = isHeytingCommutativeRing }

heytingField : HeytingField 0ℓ 0ℓ 0ℓ
heytingField = record { isHeytingField = isHeytingField }
