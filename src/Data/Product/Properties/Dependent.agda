------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of 'very dependent' map / zipWith over products
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Properties.Dependent where

open import Data.Product using (Σ; _×_; _,_; map-Σ; map-Σ′; zipWith)
open import Function.Base using (id; flip)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≗_; cong₂; refl)

private
  variable
    a b p q r s : Level
    A B C : Set a

------------------------------------------------------------------------
-- dep-map

module _ {B : A → Set b} {P : A → Set p} {Q : {x : A} → P x → B x → Set q} where

  dep-map-cong : {f g : (x : A) → B x} → {h i : ∀ {x} → (y : P x) → Q y (f x)} →
     (∀ x → f x ≡ g x) →
     (∀ {x} → (y : P x) → h y ≡ i y) →
     (v : Σ A P) → map-Σ f h v ≡ map-Σ g i v
  dep-map-cong f≗g h≗i (x , y) = cong₂ _,_ (f≗g x) (h≗i y)

------------------------------------------------------------------------
-- dep-map′

module _ {B : A → Set b} {P : Set p} {Q : P → Set q} where

  dep-map′-cong : {f g : (x : A) → B x} → {h i : (x : P) → Q x} →
     (∀ x → f x ≡ g x) →
     ((y : P) → h y ≡ i y) →
     (v : A × P) → map-Σ′ f h v ≡ map-Σ′ g i v
  dep-map′-cong f≗g h≗i (x , y) = cong₂ _,_ (f≗g x) (h≗i y)

------------------------------------------------------------------------
-- zipWith

module _ {P : A → Set p} {Q : B → Set q} {R : C → Set r} {S : (x : C) → R x → Set s} where

  zipWith-flip : (_∙_ : A → B → C) → (_∘_ : ∀ {x y} → P x → Q y → R (x ∙ y)) →
    (_*_ : (x : C) → (y : R x) → S x y) →
    {x : Σ A P} → {y : Σ B Q} →
    zipWith _∙_ _∘_ _*_ x y ≡ zipWith (flip _∙_) (flip _∘_) _*_ y x
  zipWith-flip _∙_ _∘_ _*_ = refl
