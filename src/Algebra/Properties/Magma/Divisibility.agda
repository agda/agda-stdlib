------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility over magmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Magma)
open import Data.Product using (_×_; _,_; ∃; map; swap)
open import Relation.Binary.Definitions

module Algebra.Properties.Magma.Divisibility {a ℓ} (M : Magma a ℓ) where

open Magma M

------------------------------------------------------------------------
-- Re-export divisibility relations publicly

open import Algebra.Definitions.RawMagma rawMagma public
  using (_∣_; _∤_; _∣∣_; _∤∤_)

------------------------------------------------------------------------
-- Properties of divisibility

∣-respʳ : _∣_ Respectsʳ _≈_
∣-respʳ y≈z (q , qx≈y) = q , trans qx≈y y≈z

∣-respˡ : _∣_ Respectsˡ _≈_
∣-respˡ x≈z (q , qx≈y) = q , trans (∙-congˡ (sym x≈z)) qx≈y

∣-resp : _∣_ Respects₂ _≈_
∣-resp = ∣-respʳ , ∣-respˡ

x∣yx : ∀ x y → x ∣ y ∙ x
x∣yx x y = y , refl

xy≈z⇒y∣z : ∀ x y {z} → x ∙ y ≈ z → y ∣ z
xy≈z⇒y∣z x y xy≈z = ∣-respʳ xy≈z (x∣yx y x)

------------------------------------------------------------------------
-- Properties of mutual divisibility _∣∣_

∣∣-sym : Symmetric _∣∣_
∣∣-sym = swap

∣∣-respʳ-≈ : _∣∣_ Respectsʳ _≈_
∣∣-respʳ-≈ y≈z (x∣y , y∣x) = ∣-respʳ y≈z x∣y , ∣-respˡ y≈z y∣x

∣∣-respˡ-≈ : _∣∣_ Respectsˡ _≈_
∣∣-respˡ-≈ x≈z (x∣y , y∣x) = ∣-respˡ x≈z x∣y , ∣-respʳ x≈z y∣x

∣∣-resp-≈ : _∣∣_ Respects₂ _≈_
∣∣-resp-≈ = ∣∣-respʳ-≈ , ∣∣-respˡ-≈
