{-# OPTIONS --cubical-compatible --safe #-}

module takeVecdraft where

open import Data.Fin.Base using (Fin; zero; suc; inject≤; _↑ˡ_)
open import Data.Nat.Base using (ℕ; zero; suc; _+_; _≤_; z≤n; s≤s; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; m≤m+n; +-assoc)
open import Data.Vec.Base
open import Data.Vec.Properties using (map-replicate; zipWith-replicate; padRight-trans; map-++; lookup-++ˡ)
open import Function.Base using (_∘_; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; sym; trans; subst)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    m n p : ℕ
 
------------------------------------------------------------------------

-- When you append 2 vectors together and then take the length or less than the length of the first, you get the first vector back or less than the first

take-++ : ∀ {A : Set} {m n : ℕ} → (xs : Vec A m) → (ys : Vec A n) → take m (xs ++ ys) ≡ xs
take-++ [] ys = refl
take-++ (x ∷ xs) ys = cong (x ∷_) (take-++ xs ys)

-- When you append 2 vectors together and then take the length or less than the length of the first, you get the first vector back or less than the first

{--
take-++-more : ∀ {A : Set} {m k n : ℕ} (p : ℕ) → (xs : Vec A m) → (ys : Vec A n) → (p≡m+k : p ≡ m + k) →
               take p (xs ++ ys) ≡ xs ++ take k ys

-- Proof by induction on xs
take-++-more {A} {zero} {k} {n} .k [] ys refl = refl

take-++-more {A} {suc m} {k} {n} .(suc m + k) (x ∷ xs) ys refl = 
  begin
    take (suc m + k) (x ∷ xs ++ ys)
  ≡⟨⟩
    x ∷ take (m + k) (xs ++ ys)
  ≡⟨ cong (x ∷_) (take-++-more (m + k) xs ys refl) ⟩
    x ∷ (xs ++ take k ys)
  ≡⟨⟩
    (x ∷ xs) ++ take k ys
  ∎
  --}