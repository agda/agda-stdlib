------------------------------------------------------------------------
-- The Agda standard library
--
-- List scans: properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Scans.Properties where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_; toList)
import Data.List.Properties as List
import Data.List.NonEmpty.Properties as List⁺
open import Data.List.Scans.Base
open import Function.Base using (_∘_; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≗_; refl; trans; cong; cong₂)

private
  variable
    a b : Level
    A : Set a
    B : Set b


------------------------------------------------------------------------
-- Properties

-- scanr⁺ and scanr

module _ (f : A → B → B) (e : B) where

  private
    h = List.foldr f e

  scanr⁺-defn : scanr⁺ f e ≗ List⁺.map h ∘ List⁺.tails
  scanr⁺-defn []       = refl
  scanr⁺-defn (x ∷ xs) = let eq = scanr⁺-defn xs
    in cong₂ (λ z → f x z ∷_) (cong List⁺.head eq) (cong toList eq)

  scanr-defn : scanr f e ≗ List.map h ∘ List.tails
  scanr-defn xs = cong toList (scanr⁺-defn xs)

-- scanl⁺ and scanl

module _ (f : A → B → A) where

  private
    h = List.foldl f

  scanl⁺-defn : ∀ e → scanl⁺ f e ≗ List⁺.map (h e) ∘ List⁺.inits
  scanl⁺-defn e []       = refl
  scanl⁺-defn e (x ∷ xs) = let eq = scanl⁺-defn (f e x) xs in
    cong (e ∷_) $ cong (f e x ∷_) $ trans (cong List⁺.tail eq) (List.map-∘ _)

  scanl-defn : ∀ e → scanl f e ≗ List.map (h e) ∘ List.inits
  scanl-defn e xs = cong toList (scanl⁺-defn e xs)
