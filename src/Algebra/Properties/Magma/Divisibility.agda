------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility over magmas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra using (Magma)

module Algebra.Properties.Magma.Divisibility {a ℓ} (M : Magma a ℓ) where

open import Data.Product.Base using (_,_; swap)
open import Relation.Binary.Definitions
  using (_Respects_; _Respectsˡ_; _Respectsʳ_; _Respects₂_; Symmetric)
open import Relation.Nullary.Negation.Core using (contradiction)

open Magma M

------------------------------------------------------------------------
-- Re-export divisibility relations publicly

open import Algebra.Definitions.RawMagma rawMagma public
  using (_∣_; _∤_; _∣∣_; _∤∤_; _∣ˡ_; _∤ˡ_; _∣ʳ_; _∤ʳ_; _,_)

------------------------------------------------------------------------
-- Properties of divisibility

∣-respʳ-≈ : _∣_ Respectsʳ _≈_
∣-respʳ-≈ y≈z (q , qx≈y) = q , trans qx≈y y≈z

∣-respˡ-≈ : _∣_ Respectsˡ _≈_
∣-respˡ-≈ x≈z (q , qx≈y) = q , trans (∙-congˡ (sym x≈z)) qx≈y

∣-resp-≈ : _∣_ Respects₂ _≈_
∣-resp-≈ = ∣-respʳ-≈ , ∣-respˡ-≈

x∣yx : ∀ x y → x ∣ y ∙ x
x∣yx x y = y , refl

xy≈z⇒y∣z : ∀ x y {z} → x ∙ y ≈ z → y ∣ z
xy≈z⇒y∣z x y xy≈z = ∣-respʳ-≈ xy≈z (x∣yx y x)

------------------------------------------------------------------------
-- Properties of non-divisibility

∤-respˡ-≈ : _∤_ Respectsˡ _≈_
∤-respˡ-≈ x≈y x∤z y∣z = contradiction (∣-respˡ-≈ (sym x≈y) y∣z) x∤z

∤-respʳ-≈ : _∤_ Respectsʳ _≈_
∤-respʳ-≈ x≈y z∤x z∣y = contradiction (∣-respʳ-≈ (sym x≈y) z∣y) z∤x

∤-resp-≈ : _∤_ Respects₂ _≈_
∤-resp-≈ = ∤-respʳ-≈ , ∤-respˡ-≈

------------------------------------------------------------------------
-- Properties of mutual divisibility _∣∣_

∣∣-sym : Symmetric _∣∣_
∣∣-sym = swap

∣∣-respˡ-≈ : _∣∣_ Respectsˡ _≈_
∣∣-respˡ-≈ x≈z (x∣y , y∣x) = ∣-respˡ-≈ x≈z x∣y , ∣-respʳ-≈ x≈z y∣x

∣∣-respʳ-≈ : _∣∣_ Respectsʳ _≈_
∣∣-respʳ-≈ y≈z (x∣y , y∣x) = ∣-respʳ-≈ y≈z x∣y , ∣-respˡ-≈ y≈z y∣x

∣∣-resp-≈ : _∣∣_ Respects₂ _≈_
∣∣-resp-≈ = ∣∣-respʳ-≈ , ∣∣-respˡ-≈

------------------------------------------------------------------------
-- Properties of mutual non-divisibility _∤∤_

∤∤-sym : Symmetric _∤∤_
∤∤-sym x∤∤y y∣∣x = contradiction (∣∣-sym y∣∣x) x∤∤y

∤∤-respˡ-≈ : _∤∤_ Respectsˡ _≈_
∤∤-respˡ-≈ x≈y x∤∤z y∣∣z = contradiction (∣∣-respˡ-≈ (sym x≈y) y∣∣z) x∤∤z

∤∤-respʳ-≈ : _∤∤_ Respectsʳ _≈_
∤∤-respʳ-≈ x≈y z∤∤x z∣∣y = contradiction (∣∣-respʳ-≈ (sym x≈y) z∣∣y) z∤∤x

∤∤-resp-≈ : _∤∤_ Respects₂ _≈_
∤∤-resp-≈ = ∤∤-respʳ-≈ , ∤∤-respˡ-≈


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

∣-respˡ = ∣-respˡ-≈
{-# WARNING_ON_USAGE ∣-respˡ
"Warning: ∣-respˡ was deprecated in v2.2.
Please use ∣-respˡ-≈ instead. "
#-}
∣-respʳ = ∣-respʳ-≈
{-# WARNING_ON_USAGE ∣-respʳ
"Warning: ∣-respʳ was deprecated in v2.2.
Please use ∣-respʳ-≈ instead. "
#-}
∣-resp = ∣-resp-≈
{-# WARNING_ON_USAGE ∣-resp
"Warning: ∣-resp was deprecated in v2.2.
Please use ∣-resp-≈ instead. "
#-}
