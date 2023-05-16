------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sum.Properties where

open import Level
open import Data.Sum.Base
open import Function
open import Function.Bundles using (mk↔′)
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Decidable using (map′)


private
  variable
    a b c d e f : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    E : Set e
    F : Set f

inj₁-injective : ∀ {x y} → (A ⊎ B ∋ inj₁ x) ≡ inj₁ y → x ≡ y
inj₁-injective refl = refl

inj₂-injective : ∀ {x y} → (A ⊎ B ∋ inj₂ x) ≡ inj₂ y → x ≡ y
inj₂-injective refl = refl

module _ (dec₁ : Decidable {A = A} {B = A} _≡_)
         (dec₂ : Decidable {A = B} {B = B} _≡_) where

  ≡-dec : Decidable {A = A ⊎ B} _≡_
  ≡-dec (inj₁ x) (inj₁ y) = map′ (cong inj₁) inj₁-injective (dec₁ x y)
  ≡-dec (inj₁ x) (inj₂ y) = no λ()
  ≡-dec (inj₂ x) (inj₁ y) = no λ()
  ≡-dec (inj₂ x) (inj₂ y) = map′ (cong inj₂) inj₂-injective (dec₂ x y)

swap-involutive : swap {A = A} {B = B} ∘ swap ≗ id
swap-involutive = [ (λ _ → refl) , (λ _ → refl) ]

swap-↔ : (A ⊎ B) ↔ (B ⊎ A)
swap-↔ = mk↔′ swap swap swap-involutive swap-involutive

map-id : map {A = A} {B = B} id id ≗ id
map-id (inj₁ _) = refl
map-id (inj₂ _) = refl

[,]-∘ : (f : A → B)
              {g : C → A} {h : D → A} →
              f ∘ [ g , h ] ≗ [ f ∘ g , f ∘ h ]
[,]-∘ _ (inj₁ _) = refl
[,]-∘ _ (inj₂ _) = refl

[,]-map : {f : A → B}  {g : C → D}
          {f′ : B → E} {g′ : D → E} →
          [ f′ , g′ ] ∘ map f g ≗ [ f′ ∘ f , g′ ∘ g ]
[,]-map (inj₁ _) = refl
[,]-map (inj₂ _) = refl

map-map : {f : A → B}  {g : C → D}
              {f′ : B → E} {g′ : D → F} →
              map f′ g′ ∘ map f g ≗ map (f′ ∘ f) (g′ ∘ g)
map-map (inj₁ _) = refl
map-map (inj₂ _) = refl

map₁₂-map₂₁ : {f : A → B} {g : C → D} →
                map₁ f ∘ map₂ g ≗ map₂ g ∘ map₁ f
map₁₂-map₂₁ (inj₁ _) = refl
map₁₂-map₂₁ (inj₂ _) = refl

map-assocˡ : (f : A → C) (g : B → D) (h : C → F) →
  map (map f g) h ∘ assocˡ ≗ assocˡ ∘ map f (map g h)
map-assocˡ _ _ _ (inj₁       x ) = refl
map-assocˡ _ _ _ (inj₂ (inj₁ y)) = refl
map-assocˡ _ _ _ (inj₂ (inj₂ z)) = refl

map-assocʳ : (f : A → C) (g : B → D) (h : C → F) →
  map f (map g h) ∘ assocʳ ≗ assocʳ ∘ map (map f g) h
map-assocʳ _ _ _ (inj₁ (inj₁ x)) = refl
map-assocʳ _ _ _ (inj₁ (inj₂ y)) = refl
map-assocʳ _ _ _ (inj₂       z ) = refl

[,]-cong : {f f′ : A → B} {g g′ : C → B} →
           f ≗ f′ → g ≗ g′ →
           [ f , g ] ≗ [ f′ , g′ ]
[,]-cong = [_,_]

[-,]-cong : {f f′ : A → B} {g : C → B} →
            f ≗ f′ →
            [ f , g ] ≗ [ f′ , g ]
[-,]-cong = [_, (λ _ → refl) ]

[,-]-cong : {f : A → B} {g g′ : C → B} →
            g ≗ g′ →
            [ f , g ] ≗ [ f , g′ ]
[,-]-cong = [ (λ _ → refl) ,_]

map-cong : {f f′ : A → B} {g g′ : C → D} →
           f ≗ f′ → g ≗ g′ →
           map f g ≗ map f′ g′
map-cong f≗f′ g≗g′ (inj₁ x) = cong inj₁ (f≗f′ x)
map-cong f≗f′ g≗g′ (inj₂ x) = cong inj₂ (g≗g′ x)

map₁-cong : {f f′ : A → B} →
            f ≗ f′ →
            map₁ {B = C} f ≗ map₁ f′
map₁-cong f≗f′ = [-,]-cong ((cong inj₁) ∘ f≗f′)

map₂-cong : {g g′ : C → D} →
            g ≗ g′ →
            map₂ {A = A} g ≗ map₂ g′
map₂-cong g≗g′ = [,-]-cong ((cong inj₂) ∘ g≗g′)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

[,]-∘-distr = [,]-∘
{-# WARNING_ON_USAGE [,]-∘-distr
"Warning: [,]-∘-distr was deprecated in v2.0.
Please use [,]-∘ instead."
#-}

[,]-map-commute = [,]-map
{-# WARNING_ON_USAGE [,]-map-commute
"Warning: [,]-map-commute was deprecated in v2.0.
Please use [,]-map instead."
#-}

map-commute = map-map
{-# WARNING_ON_USAGE map-commute
"Warning: map-commute was deprecated in v2.0.
Please use map-map instead."
#-}

map₁₂-commute = map₁₂-map₂₁
{-# WARNING_ON_USAGE map₁₂-commute
"Warning: map₁₂-commute was deprecated in v2.0.
Please use map₁₂-map₂₁ instead."
#-}
