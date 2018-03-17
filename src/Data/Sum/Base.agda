------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums (disjoint unions)
------------------------------------------------------------------------

module Data.Sum.Base where

open import Function using (_∘_; _-[_]-_)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definition

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

{-# FOREIGN GHC type AgdaEither a b c d = Either c d #-}
{-# COMPILE GHC _⊎_ = data MAlonzo.Code.Data.Sum.AgdaEither (Left | Right) #-}

------------------------------------------------------------------------
-- Functions

[_,_] : ∀ {a b c} {A : Set a} {B : Set b} {C : A ⊎ B → Set c} →
        ((x : A) → C (inj₁ x)) → ((x : B) → C (inj₂ x)) →
        ((x : A ⊎ B) → C x)
[ f , g ] (inj₁ x) = f x
[ f , g ] (inj₂ y) = g y

[_,_]′ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
         (A → C) → (B → C) → (A ⊎ B → C)
[_,_]′ = [_,_]

map : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
map f g = [ inj₁ ∘ f , inj₂ ∘ g ]

infixr 1 _-⊎-_

_-⊎-_ : ∀ {a b c d} {A : Set a} {B : Set b} →
        (A → B → Set c) → (A → B → Set d) → (A → B → Set (c ⊔ d))
f -⊎- g = f -[ _⊎_ ]- g
