------------------------------------------------------------------------
-- The Agda standard library
--
-- Some items and theory for Magma
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Magma)
open import Algebra.Definitions using (Commutative; LeftQuotient)
open import Data.Product using (_×_; _,_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel; _Respects_; _Respects₂_)
open import Relation.Nullary using (¬_)

module Algebra.Properties.Magma {a ℓ} (M : Magma a ℓ) where

open Magma M

------------------------------------------------------------------------------
-- The divisibility relation
------------------------------------------------------------------------------

infix 5 _∣_ _∤_ _∣∣_ _¬∣∣_

private C = Carrier

_∣_ : Rel C (a ⊔ ℓ)                   -- x ∣ y  denotes  x divides y
x ∣ y =  LeftQuotient _≈_ _∙_ y x     -- as  y ≈ q ∙ x  for some q.

_∤_ : Rel C (a ⊔ ℓ)
_∤_ x = ¬_ ∘ _∣_ x

_∣∣_ : Rel C (a ⊔ ℓ)
x ∣∣ y = x ∣ y × y ∣ x

-- _∣∣_ is mutual divisibility.
-- The elements related by _∣∣_ are called associated  (when in a cancellative
-- monoid).
-- For a cancellative monoid, it follows from
-- x ∣∣ y  that x and y differ only in a certain invertible factor.
-- It will be proved further that  gcd a b  is unique, in the sense that
-- g g' : GCD a b → g ∣∣ g'.

_¬∣∣_ : Rel C (a ⊔ ℓ)
_¬∣∣_ x =  ¬_ ∘ _∣∣_ x

------------------------------------------------------------------------------
-- Properties of divisibility _∣_ in Magma.
------------------------------------------------------------------------------

∣-respˡ : {y : C} → (_∣ y) Respects _≈_
∣-respˡ x≈x' (q , y≈qx) =  (q , trans y≈qx (∙-congˡ x≈x'))

∣-respʳ : {x : C} → (x ∣_) Respects _≈_
∣-respʳ y≈y' (q , y≈qx) =  (q , trans (sym y≈y') y≈qx)

∣-resp : _∣_ Respects₂ _≈_
∣-resp = ((\{x y y'} → ∣-respʳ {x} {y} {y'}) , (\{y x x'} → ∣-respˡ {y} {x} {x'}))

x∣yx : {x : C} → (y : C) → x ∣ (y ∙ x)
x∣yx y = (y , refl)

x∣xy : Commutative _≈_ _∙_ → {x : C} → (y : C) → x ∣ (x ∙ y)
x∣xy comm {x} y = (y , comm x y)

bothFactors-∣ : Commutative _≈_ _∙_ → (x y : C) → x ∣ (y ∙ x) × y ∣ (y ∙ x)
bothFactors-∣ comm x y = ((y , refl) , (x , comm y x))

bothFactors-∣≈ : Commutative _≈_ _∙_ → (x y z : C) → z ≈ y ∙ x → x ∣ z × y ∣ z
bothFactors-∣≈ comm x y z z≈yx =
  let (x∣yx , y∣yx) = bothFactors-∣ comm x y
  in
  (∣-respʳ (sym z≈yx) x∣yx , ∣-respʳ (sym z≈yx) y∣yx)
