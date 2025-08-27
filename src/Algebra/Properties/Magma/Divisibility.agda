------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility over magmas
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Magma)

module Algebra.Properties.Magma.Divisibility {a ℓ} (M : Magma a ℓ) where

open import Data.Product.Base using (_,_; swap)
open import Relation.Binary.Definitions
  using (_Respects_; _Respectsˡ_; _Respectsʳ_; _Respects₂_; Symmetric)
open import Relation.Nullary.Negation.Core using (contradiction)

open Magma M

------------------------------------------------------------------------
-- Re-export divisibility relations publicly

open import Algebra.Definitions.RawMagma rawMagma public
  using (_∣_; _∤_; _∥_; _∦_; _∣ˡ_; _∤ˡ_; _∣ʳ_; _∤ʳ_; _,_)

------------------------------------------------------------------------
-- Properties of right divisibility

∣ʳ-respʳ-≈ : _∣ʳ_ Respectsʳ _≈_
∣ʳ-respʳ-≈ y≈z (q , qx≈y) = q , trans qx≈y y≈z

∣ʳ-respˡ-≈ : _∣ʳ_ Respectsˡ _≈_
∣ʳ-respˡ-≈ x≈z (q , qx≈y) = q , trans (∙-congˡ (sym x≈z)) qx≈y

∣ʳ-resp-≈ : _∣ʳ_ Respects₂ _≈_
∣ʳ-resp-≈ = ∣ʳ-respʳ-≈ , ∣ʳ-respˡ-≈

x∣ʳyx : ∀ x y → x ∣ʳ y ∙ x
x∣ʳyx x y = y , refl

xy≈z⇒y∣ʳz : ∀ x y {z} → x ∙ y ≈ z → y ∣ʳ z
xy≈z⇒y∣ʳz x y xy≈z = x , xy≈z

------------------------------------------------------------------------
-- Properties of left divisibility

∣ˡ-respʳ-≈ : _∣ˡ_ Respectsʳ _≈_
∣ˡ-respʳ-≈ y≈z (q , xq≈y) = q , trans xq≈y y≈z

∣ˡ-respˡ-≈ : _∣ˡ_ Respectsˡ _≈_
∣ˡ-respˡ-≈ x≈z (q , xq≈y) = q , trans (∙-congʳ (sym x≈z)) xq≈y

∣ˡ-resp-≈ : _∣ˡ_ Respects₂ _≈_
∣ˡ-resp-≈ = ∣ˡ-respʳ-≈ , ∣ˡ-respˡ-≈

x∣ˡxy : ∀ x y → x ∣ˡ x ∙ y
x∣ˡxy x y = y , refl

xy≈z⇒x∣ˡz : ∀ x y {z} → x ∙ y ≈ z → x ∣ˡ z
xy≈z⇒x∣ˡz x y xy≈z = y , xy≈z

------------------------------------------------------------------------
-- Properties of non-divisibility

∤-respˡ-≈ : _∤_ Respectsˡ _≈_
∤-respˡ-≈ x≈y x∤z y∣ʳz = contradiction (∣ʳ-respˡ-≈ (sym x≈y) y∣ʳz) x∤z

∤-respʳ-≈ : _∤_ Respectsʳ _≈_
∤-respʳ-≈ x≈y z∤x z∣ʳy = contradiction (∣ʳ-respʳ-≈ (sym x≈y) z∣ʳy) z∤x

∤-resp-≈ : _∤_ Respects₂ _≈_
∤-resp-≈ = ∤-respʳ-≈ , ∤-respˡ-≈

------------------------------------------------------------------------
-- Properties of mutual divisibility _∥_

∥-sym : Symmetric _∥_
∥-sym = swap

∥-respˡ-≈ : _∥_ Respectsˡ _≈_
∥-respˡ-≈ x≈z (x∣ʳy , y∣ʳx) = ∣ʳ-respˡ-≈ x≈z x∣ʳy , ∣ʳ-respʳ-≈ x≈z y∣ʳx

∥-respʳ-≈ : _∥_ Respectsʳ _≈_
∥-respʳ-≈ y≈z (x∣ʳy , y∣ʳx) = ∣ʳ-respʳ-≈ y≈z x∣ʳy , ∣ʳ-respˡ-≈ y≈z y∣ʳx

∥-resp-≈ : _∥_ Respects₂ _≈_
∥-resp-≈ = ∥-respʳ-≈ , ∥-respˡ-≈

------------------------------------------------------------------------
-- Properties of mutual non-divisibility _∤∤_

∦-sym : Symmetric _∦_
∦-sym x∦y y∥x = contradiction (∥-sym y∥x) x∦y

∦-respˡ-≈ : _∦_ Respectsˡ _≈_
∦-respˡ-≈ x≈y x∦z y∥z = contradiction (∥-respˡ-≈ (sym x≈y) y∥z) x∦z

∦-respʳ-≈ : _∦_ Respectsʳ _≈_
∦-respʳ-≈ x≈y z∦x z∥y = contradiction (∥-respʳ-≈ (sym x≈y) z∥y) z∦x

∦-resp-≈ : _∦_ Respects₂ _≈_
∦-resp-≈ = ∦-respʳ-≈ , ∦-respˡ-≈


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

∣-respˡ = ∣ʳ-respˡ-≈
{-# WARNING_ON_USAGE ∣-respˡ
"Warning: ∣-respˡ was deprecated in v2.2.
Please use ∣ʳ-respˡ-≈ instead. "
#-}
∣-respʳ = ∣ʳ-respʳ-≈
{-# WARNING_ON_USAGE ∣-respʳ
"Warning: ∣-respʳ was deprecated in v2.2.
Please use ∣ʳ-respʳ-≈ instead. "
#-}
∣-resp = ∣ʳ-resp-≈
{-# WARNING_ON_USAGE ∣-resp
"Warning: ∣-resp was deprecated in v2.2.
Please use ∣ʳ-resp-≈ instead. "
#-}

-- Version 2.3

∣∣-sym = ∥-sym
{-# WARNING_ON_USAGE ∣∣-sym
"Warning: ∣∣-sym was deprecated in v2.3.
Please use ∥-sym instead. "
#-}
∣∣-respˡ-≈ = ∥-respˡ-≈
{-# WARNING_ON_USAGE ∣∣-respˡ-≈
"Warning: ∣∣-respˡ-≈ was deprecated in v2.3.
Please use ∥-respˡ-≈ instead. "
#-}
∣∣-respʳ-≈ = ∥-respʳ-≈
{-# WARNING_ON_USAGE ∣∣-respʳ-≈
"Warning: ∣∣-respʳ-≈ was deprecated in v2.3.
Please use ∥-respʳ-≈ instead. "
#-}
∣∣-resp-≈ = ∥-resp-≈
{-# WARNING_ON_USAGE ∣∣-resp-≈
"Warning: ∣∣-resp-≈ was deprecated in v2.3.
Please use ∥-resp-≈ instead. "
#-}
∤∤-sym = ∦-sym
{-# WARNING_ON_USAGE ∤∤-sym
"Warning: ∤∤-sym was deprecated in v2.3.
Please use ∦-sym instead. "
#-}
∤∤-respˡ-≈ = ∦-respˡ-≈
{-# WARNING_ON_USAGE ∤∤-respˡ-≈
"Warning: ∤∤-respˡ-≈ was deprecated in v2.3.
Please use ∦-respˡ-≈ instead. "
#-}
∤∤-respʳ-≈ = ∦-respʳ-≈
{-# WARNING_ON_USAGE ∤∤-respʳ-≈
"Warning: ∤∤-respʳ-≈ was deprecated in v2.3.
Please use ∦-respʳ-≈ instead. "
#-}
∤∤-resp-≈ = ∦-resp-≈
{-# WARNING_ON_USAGE ∤∤-resp-≈
"Warning: ∤∤-resp-≈ was deprecated in v2.3.
Please use ∦-resp-≈ instead. "
#-}

∣-respʳ-≈ = ∣ʳ-respʳ-≈
{-# WARNING_ON_USAGE ∣-respʳ-≈
"Warning: ∣-respʳ-≈ was deprecated in v2.3.
Please use ∣ʳ-respʳ-≈ instead. "
#-}

∣-respˡ-≈ = ∣ʳ-respˡ-≈
{-# WARNING_ON_USAGE ∣-respˡ-≈
"Warning: ∣-respˡ-≈ was deprecated in v2.3.
Please use ∣ʳ-respˡ-≈ instead. "
#-}

∣-resp-≈ = ∣ʳ-resp-≈
{-# WARNING_ON_USAGE ∣-resp-≈
"Warning: ∣-resp-≈ was deprecated in v2.3.
Please use ∣ʳ-resp-≈ instead. "
#-}

x∣yx = x∣ʳyx
{-# WARNING_ON_USAGE x∣yx
"Warning: x∣yx was deprecated in v2.3.
Please use x∣ʳyx instead. "
#-}

xy≈z⇒y∣z = xy≈z⇒y∣ʳz
{-# WARNING_ON_USAGE xy≈z⇒y∣z
"Warning: xy≈z⇒y∣z was deprecated in v2.3.
Please use xy≈z⇒y∣ʳz instead. "
#-}
