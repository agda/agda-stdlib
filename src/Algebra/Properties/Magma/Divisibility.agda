------------------------------------------------------------------------
-- The Agda standard library
--
-- Divisibility over magmas
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Magma)
open import Data.Product using (_×_; _,_; ∃; map)
open import Relation.Binary.Definitions

module Algebra.Properties.Magma.Divisibility {a ℓ} (M : Magma a ℓ) where

open Magma M

------------------------------------------------------------------------------
-- Re-export divisibility relations publicly

open import Algebra.Divisibility _≈_ _∙_ as Div public
  using (_∣_; _∤_; _∣∣_; _¬∣∣_)

------------------------------------------------------------------------------
-- Properties of divisibility

∣-respʳ : _∣_ Respectsʳ _≈_
∣-respʳ = Div.∣-respʳ trans

∣-respˡ : _∣_ Respectsˡ _≈_
∣-respˡ = Div.∣-respˡ sym trans ∙-congˡ

∣-resp : _∣_ Respects₂ _≈_
∣-resp = Div.∣-resp sym trans ∙-congˡ

x∣yx : ∀ x y → x ∣ y ∙ x
x∣yx x y = y , refl

xy≈z⇒y∣z : ∀ x y {z} → x ∙ y ≈ z → y ∣ z
xy≈z⇒y∣z x y xy≈z = ∣-respʳ xy≈z (x∣yx y x)
