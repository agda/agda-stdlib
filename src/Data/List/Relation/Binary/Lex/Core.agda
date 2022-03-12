------------------------------------------------------------------------
-- The Agda standard library
--
-- Lexicographic ordering of lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Lex.Core where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.List.Base using (List; []; _∷_)
open import Function.Base using (_∘_; flip; id)
open import Level using (Level; _⊔_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.Core using (Rel)
open import Data.List.Relation.Binary.Pointwise.Base
   using (Pointwise; []; _∷_; head; tail)

private
  variable
    a ℓ₁ ℓ₂ : Level

-- The lexicographic ordering itself can be either strict or non-strict,
-- depending on whether type P is inhabited.

data Lex {A : Set a} (P : Set)
         (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) :
         Rel (List A) (a ⊔ ℓ₁ ⊔ ℓ₂) where
  base : P                             → Lex P _≈_ _≺_ []       []
  halt : ∀ {y ys}                      → Lex P _≈_ _≺_ []       (y ∷ ys)
  this : ∀ {x xs y ys} (x≺y : x ≺ y)   → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)
  next : ∀ {x xs y ys} (x≈y : x ≈ y)
         (xs<ys : Lex P _≈_ _≺_ xs ys) → Lex P _≈_ _≺_ (x ∷ xs) (y ∷ ys)

----------------------------------------------------------------------
-- Lexicographic orderings, using a strict ordering as the base

Lex-< : {A : Set a} (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) →
        Rel (List A) (a ⊔ ℓ₁ ⊔ ℓ₂)
Lex-< = Lex ⊥

Lex-≤ : {A : Set a} (_≈_ : Rel A ℓ₁) (_≺_ : Rel A ℓ₂) →
        Rel (List A) (a ⊔ ℓ₁ ⊔ ℓ₂)
Lex-≤ = Lex ⊤
