------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of coinductive lists and their operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --guardedness #-}

module Codata.Musical.Colist.Properties where

open import Level using (Level)
open import Codata.Musical.Notation using (♭; ∞; ♯_)
open import Codata.Musical.Colist.Base using (Colist; []; _∷_)
open import Function.Base using (_∋_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)

private
  variable
    a b : Level
    A : Set a
    B : Set b

∷-injectiveˡ : ∀ {x y xs ys} → (Colist A ∋ x ∷ xs) ≡ y ∷ ys → x ≡ y
∷-injectiveˡ refl = refl

∷-injectiveʳ : ∀ {x y xs ys} → (Colist A ∋ x ∷ xs) ≡ y ∷ ys → xs ≡ ys
∷-injectiveʳ refl = refl
