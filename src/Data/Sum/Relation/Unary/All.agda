------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous All-predicate for disjoint sums
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Relation.Unary.All where

open import Data.Sum       using (_⊎_); open _⊎_
open import Level          using (Level; _⊔_)
open import Relation.Unary using (Pred)

private
  variable
    a b c p q : Level
    A B : Set _

data All₂ {A : Set a} {B : Set b} (P : Pred A p) (Q : Pred B q)
       : Pred (A ⊎ B) (a ⊔ b ⊔ p ⊔ q) where
  inj₁ : ∀ {a} → P a → All₂ P Q (inj₁ a)
  inj₂ : ∀ {b} → Q b → All₂ P Q (inj₂ b)

-- Elimination

[_,_] : ∀ {P : Pred A p} {Q : Pred B q} {C : (x : A ⊎ B) → All₂ P Q x → Set c} →
        ((x : A) (y : P x) → C (inj₁ x) (inj₁ y)) →
        ((x : B) (y : Q x) → C (inj₂ x) (inj₂ y)) →
        (x : A ⊎ B) (y : All₂ P Q x) → C x y
[ f , g ] (inj₁ x) (inj₁ y) = f x y
[ f , g ] (inj₂ x) (inj₂ y) = g x y
