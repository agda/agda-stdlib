------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Properties where

open import Level
open import Data.Sum.Base
open import Function
open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (yes; no)
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

map-id : map {A = A} {B = B} id id ≗ id
map-id (inj₁ _) = refl
map-id (inj₂ _) = refl

[,]-∘-distr : (f : A → B)
              {g : C → A} {h : D → A} →
              f ∘ [ g , h ] ≗ [ f ∘ g , f ∘ h ]
[,]-∘-distr _ (inj₁ _) = refl
[,]-∘-distr _ (inj₂ _) = refl

[,]-map-commute : {f : A → B}  {g : C → D}
                  {f′ : B → E} {g′ : D → E} →
                  [ f′ , g′ ] ∘ map f g ≗ [ f′ ∘ f , g′ ∘ g ]
[,]-map-commute (inj₁ _) = refl
[,]-map-commute (inj₂ _) = refl

map-commute : {f : A → B}  {g : C → D}
              {f′ : B → E} {g′ : D → F} →
              map f′ g′ ∘ map f g ≗ map (f′ ∘ f) (g′ ∘ g)
map-commute (inj₁ _) = refl
map-commute (inj₂ _) = refl

map₁₂-commute : {f : A → B} {g : C → D} →
                map₁ f ∘ map₂ g ≗ map₂ g ∘ map₁ f
map₁₂-commute (inj₁ _) = refl
map₁₂-commute (inj₂ _) = refl

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
