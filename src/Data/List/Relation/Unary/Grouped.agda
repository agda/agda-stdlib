------------------------------------------------------------------------
-- The Agda standard library
--
-- Property that elements are grouped
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Unary.Grouped where

open import Data.List.Base using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_; all?)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import Relation.Binary as B using (REL; Rel)
open import Relation.Unary as U using (Pred)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable as Dec using (yes; ¬?; _⊎-dec_; _×-dec_)
open import Level using (Level; _⊔_)

private
  variable
    a ℓ : Level
    A : Set a
    x y : A
    xs : List A

------------------------------------------------------------------------
-- Definition

infixr 5 _∷≉_ _∷≈_

data Grouped {A : Set a} (_≈_ : Rel A ℓ) : Pred (List A) (a ⊔ ℓ) where
  [] : Grouped _≈_ []
  _∷≉_ : All (λ y → ¬ (x ≈ y)) xs → Grouped _≈_ xs → Grouped _≈_ (x ∷ xs)
  _∷≈_ : x ≈ y → Grouped _≈_ (y ∷ xs) → Grouped _≈_ (x ∷ y ∷ xs)

------------------------------------------------------------------------
-- Basic properties

module _ {_≈_ : Rel A ℓ} where

  grouped? : B.Decidable _≈_ → U.Decidable (Grouped _≈_)
  grouped? _≟_ [] = yes []
  grouped? _≟_ (x ∷ []) = yes ([] ∷≉ [])
  grouped? _≟_ (x ∷ y ∷ xs) =
    Dec.map′ from to ((x ≟ y ⊎-dec all? (λ z → ¬? (x ≟ z)) (y ∷ xs)) ×-dec (grouped? _≟_ (y ∷ xs)))
    where
    from : ((x ≈ y) ⊎ All (λ z → ¬ (x ≈ z)) (y ∷ xs)) × Grouped _≈_ (y ∷ xs) → Grouped _≈_ (x ∷ y ∷ xs)
    from (inj₁ x≈y          , grouped[y∷xs]) = x≈y          ∷≈ grouped[y∷xs]
    from (inj₂ all[x≉,y∷xs] , grouped[y∷xs]) = all[x≉,y∷xs] ∷≉ grouped[y∷xs]

    to : Grouped _≈_ (x ∷ y ∷ xs) → ((x ≈ y) ⊎ All (λ z → ¬ (x ≈ z)) (y ∷ xs)) × Grouped _≈_ (y ∷ xs)
    to (all[x≉,y∷xs] ∷≉ grouped[y∷xs]) = inj₂ all[x≉,y∷xs] , grouped[y∷xs]
    to (x≈y          ∷≈ grouped[y∷xs]) = inj₁ x≈y , grouped[y∷xs]
