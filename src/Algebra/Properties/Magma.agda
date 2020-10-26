------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Magma
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Magma)
open import Algebra.Definitions using (Commutative; module Divisibility)
open import Data.Product using (_×_; _,_; ∃; map)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; _Respects_; _Respects₂_)
open import Relation.Nullary using (¬_)

module Algebra.Properties.Magma {a ℓ} (M : Magma a ℓ) where

open Magma M

------------------------------------------------------------------------------
-- Properties of divisibility
------------------------------------------------------------------------------

open Divisibility {A = Carrier} _≈_ _∙_ public using (_∣_; _∤_; _∣∣_; _¬∣∣_)

∣-respˡ : ∀ {y} → (_∣ y) Respects _≈_
∣-respˡ x≈x' (q , y≈qx) = q , trans y≈qx (∙-congˡ x≈x')

∣-respʳ : ∀ {x} → (x ∣_) Respects _≈_
∣-respʳ y≈y' (q , y≈qx) = q , trans (sym y≈y') y≈qx

∣-resp : _∣_ Respects₂ _≈_
∣-resp = ∣-respʳ , ∣-respˡ

x∣yx : ∀ x y → x ∣ (y ∙ x)
x∣yx _ y = y , refl

x∣xy : Commutative _≈_ _∙_ → ∀ x y → x ∣ (x ∙ y)
x∣xy comm x y = y , comm x y

bothFactors-∣ : Commutative _≈_ _∙_ → (∀ x y → x ∣ (y ∙ x) × y ∣ (y ∙ x))
bothFactors-∣ comm x y = (y , refl) , (x , comm y x)

bothFactors-∣≈ : Commutative _≈_ _∙_ → (∀ x y z → z ≈ y ∙ x → x ∣ z × y ∣ z)
bothFactors-∣≈ comm x y z z≈yx =
  let (x∣yx , y∣yx) = bothFactors-∣ comm x y
  in
  (∣-respʳ (sym z≈yx) x∣yx) , (∣-respʳ (sym z≈yx) y∣yx)
