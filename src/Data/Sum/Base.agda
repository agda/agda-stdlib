------------------------------------------------------------------------
-- The Agda standard library
--
-- Sums (disjoint unions)
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Sum.Base where

open import Function using (_∘_; _-[_]-_ ; id)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Level using (_⊔_)

------------------------------------------------------------------------
-- Definition

infixr 1 _⊎_

data _⊎_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

{-# FOREIGN GHC type AgdaEither a b c d = Either c d #-}
{-# COMPILE GHC _⊎_ = data AgdaEither (Left | Right) #-}

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

swap : ∀ {a b} {A : Set a} {B : Set b} → A ⊎ B → B ⊎ A
swap (inj₁ x) = inj₂ x
swap (inj₂ x) = inj₁ x

map : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} →
      (A → C) → (B → D) → (A ⊎ B → C ⊎ D)
map f g = [ inj₁ ∘ f , inj₂ ∘ g ]

map₁ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}→
       (A → C) → (A ⊎ B → C ⊎ B)
map₁ f = map f id

map₂ : ∀ {a b d} {A : Set a} {B : Set b} {D : Set d} →
       (B → D) → (A ⊎ B → A ⊎ D)
map₂ = map id

infixr 1 _-⊎-_
_-⊎-_ : ∀ {a b c d} {A : Set a} {B : Set b} →
        (A → B → Set c) → (A → B → Set d) → (A → B → Set (c ⊔ d))
f -⊎- g = f -[ _⊎_ ]- g

module _ {p} {P : Set p} where

-- Conversion back and forth with Dec

  fromDec : Dec P → P ⊎ ¬ P
  fromDec (yes p) = inj₁ p
  fromDec (no ¬p) = inj₂ ¬p

  toDec : P ⊎ ¬ P → Dec P
  toDec (inj₁ p)  = yes p
  toDec (inj₂ ¬p) = no ¬p
