------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vec-related properties that depend on the K rule or make use
-- of heterogeneous equality
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Vec.Properties.WithK where

open import Data.Nat.Base
open import Data.Nat.Properties using (+-assoc)
open import Data.Vec.Base
open import Relation.Binary.PropositionalEquality as P using (_≡_; refl)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)

------------------------------------------------------------------------
-- _[_]=_

module _ {a} {A : Set a} where

  []=-irrelevant : ∀ {n} {xs : Vec A n} {i x} →
                    (p q : xs [ i ]= x) → p ≡ q
  []=-irrelevant here            here             = refl
  []=-irrelevant (there xs[i]=x) (there xs[i]=x') =
    P.cong there ([]=-irrelevant xs[i]=x xs[i]=x')

------------------------------------------------------------------------
-- _++_

module _ {a} {A : Set a} where

  ++-assoc : ∀ {m n k} (xs : Vec A m) (ys : Vec A n) (zs : Vec A k) →
             (xs ++ ys) ++ zs ≅ xs ++ (ys ++ zs)
  ++-assoc         []       ys zs = refl
  ++-assoc {suc m} (x ∷ xs) ys zs =
    H.icong (Vec A) (+-assoc m _ _) (x ∷_) (++-assoc xs ys zs)

------------------------------------------------------------------------
-- foldr

foldr-cong : ∀ {a b} {A : Set a}
             {B : ℕ → Set b} {f : ∀ {n} → A → B n → B (suc n)} {d}
             {C : ℕ → Set b} {g : ∀ {n} → A → C n → C (suc n)} {e} →
             (∀ {n x} {y : B n} {z : C n} → y ≅ z → f x y ≅ g x z) →
             d ≅ e → ∀ {n} (xs : Vec A n) →
             foldr B f d xs ≅ foldr C g e xs
foldr-cong _   d≅e []       = d≅e
foldr-cong f≅g d≅e (x ∷ xs) = f≅g (foldr-cong f≅g d≅e xs)

------------------------------------------------------------------------
-- foldl

foldl-cong : ∀ {a b} {A : Set a}
             {B : ℕ → Set b} {f : ∀ {n} → B n → A → B (suc n)} {d}
             {C : ℕ → Set b} {g : ∀ {n} → C n → A → C (suc n)} {e} →
             (∀ {n x} {y : B n} {z : C n} → y ≅ z → f y x ≅ g z x) →
             d ≅ e → ∀ {n} (xs : Vec A n) →
             foldl B f d xs ≅ foldl C g e xs
foldl-cong _   d≅e []       = d≅e
foldl-cong f≅g d≅e (x ∷ xs) = foldl-cong f≅g (f≅g d≅e) xs

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.0

[]=-irrelevance = []=-irrelevant
{-# WARNING_ON_USAGE []=-irrelevance
"Warning: []=-irrelevance was deprecated in v1.0.
Please use []=-irrelevant instead."
#-}
