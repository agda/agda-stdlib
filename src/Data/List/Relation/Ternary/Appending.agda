------------------------------------------------------------------------
-- The Agda standard library
--
-- Generalised view of appending two lists into one.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Ternary.Appending {a b c} {A : Set a} {B : Set b} {C : Set c} where

open import Level using (Level; _⊔_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product as Prod using (∃₂; _×_; _,_; -,_)
open import Relation.Binary using (REL)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)

private
  variable
    l r : Level
    L : REL A C l
    R : REL B C r
    as : List A
    bs : List B
    cs : List C

------------------------------------------------------------------------
-- Definition

module _ (L : REL A C l) (R : REL B C r) where

  infixr 5 _∷_ []++_

  data Appending : List A → List B → List C → Set (a ⊔ b ⊔ c ⊔ l ⊔ r) where
    []++_  : ∀ {bs cs} → Pointwise R bs cs → Appending [] bs cs
    _∷_    : ∀ {a as bs c cs} → L a c → Appending as bs cs → Appending (a ∷ as) bs (c ∷ cs)

------------------------------------------------------------------------
-- Functions manipulating Appending

infixr 5 _++_

_++_ : ∀ {cs₁ cs₂ : List C} → Pointwise L as cs₁ → Pointwise R bs cs₂ →
       Appending L R as bs (cs₁ List.++ cs₂)
[]       ++ rs = []++ rs
(l ∷ ls) ++ rs = l ∷ (ls ++ rs)

-- extract the "proper" equality split from the pointwise relation
break : Appending L R as bs cs → ∃₂ λ cs₁ cs₂ →
        cs₁ List.++ cs₂ ≡ cs × Pointwise L as cs₁ × Pointwise R bs cs₂
break ([]++ rs) = -, -, (refl , [] , rs)
break (l ∷ lrs) =
  let (_ , _ , eq , ls , rs) = break lrs in
  -, -, (cong (_ ∷_) eq , l ∷ ls , rs)
