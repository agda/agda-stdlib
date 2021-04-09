------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous `All` predicate for disjoint sums
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Relation.Unary.All where

open import Data.Sum.Base  using (_⊎_; inj₁; inj₂)
open import Level          using (Level; _⊔_)
open import Relation.Unary using (Pred)

private
  variable
    a b c p q : Level
    A B : Set _
    P Q : Pred A p

------------------------------------------------------------------------
-- Definition

data All {A : Set a} {B : Set b} (P : Pred A p) (Q : Pred B q)
         : Pred (A ⊎ B) (a ⊔ b ⊔ p ⊔ q) where
  inj₁ : ∀ {a} → P a → All P Q (inj₁ a)
  inj₂ : ∀ {b} → Q b → All P Q (inj₂ b)

------------------------------------------------------------------------
-- Operations

-- Elimination

[_,_] : ∀ {C : (x : A ⊎ B) → All P Q x → Set c} →
        ((x : A) (y : P x) → C (inj₁ x) (inj₁ y)) →
        ((x : B) (y : Q x) → C (inj₂ x) (inj₂ y)) →
        (x : A ⊎ B) (y : All P Q x) → C x y
[ f , g ] (inj₁ x) (inj₁ y) = f x y
[ f , g ] (inj₂ x) (inj₂ y) = g x y
