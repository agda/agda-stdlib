------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary vectors
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Vec.Binary.Properties where

open import Data.Nat.Binary.Base
open import Data.Vec.Binary.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

private
  variable
    a : Level
    A : Set a
    n : ℕᵇ

-- Properties of head, tail, and _∷_
------------------------------------------------------------------------

head-∷ : ∀ x (xs : Vecᵇ A n) → head (x ∷ xs) ≡ x
head-∷ x [] = refl
head-∷ x (_ ∷⟨ _ / _ ⟩) = refl
head-∷ x (_ × _ ∷⟨ _ / _ ⟩) = refl

merge-∷ : ∀ x₁ x₂ (xs₁ xs₂ : Vecᵇ A n) → merge (x₁ ∷ xs₁) (x₂ ∷ xs₂) ≡ x₁ × x₂ ∷⟨ xs₁ / xs₂ ⟩
merge-∷ x₁ x₂ [] [] = refl
merge-∷ x₁ x₂ (x ∷⟨ xs₁ / xs₂ ⟩) (x₃ ∷⟨ xs₃ / xs₄ ⟩) = refl
merge-∷ x₁ x₂ (y₁ × z₁ ∷⟨ ls₁ / rs₁ ⟩) (y₂ × z₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ (x₁ × x₂ ∷⟨_/_⟩) (merge-∷ y₁ z₁ ls₁ rs₁) (merge-∷ y₂ z₂ ls₂ rs₂)

tail-∷ : ∀ x (xs : Vecᵇ A n) → tail (x ∷ xs) ≡ xs
tail-∷ x [] = refl
tail-∷ x (y ∷⟨ ls / rs ⟩) = refl
tail-∷ x (y × z ∷⟨ ls / rs ⟩) = merge-∷ y z ls rs

∷-merge : ∀ x (ls rs : Vecᵇ A (suc n)) → x ∷ merge ls rs ≡ x ∷⟨ ls / rs ⟩
∷-merge {n = zero} x (y₁ ∷⟨ [] / [] ⟩) (y₂ ∷⟨ [] / [] ⟩) = refl
∷-merge {n = 2[1+ n ]} x (y₁ ∷⟨ ls₁ / rs₁ ⟩) (y₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ (x ∷⟨_/_⟩) (∷-merge y₁ ls₁ rs₁) (∷-merge y₂ ls₂ rs₂)
∷-merge {n = 1+[2 n ]} x (y₁ × z₁ ∷⟨ ls₁ / rs₁ ⟩) (y₂ × z₂ ∷⟨ ls₂ / rs₂ ⟩) = refl

∷-head-tail : ∀ (xs : Vecᵇ A (suc n)) → head xs ∷ tail xs ≡ xs
∷-head-tail {n = zero} (x ∷⟨ [] / [] ⟩) = refl
∷-head-tail {n = 2[1+ n ]} (x ∷⟨ ls / rs ⟩) = ∷-merge x ls rs
∷-head-tail {n = 1+[2 n ]} (x × y ∷⟨ ls / rs ⟩) = refl
