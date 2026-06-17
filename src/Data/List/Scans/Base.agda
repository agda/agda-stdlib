------------------------------------------------------------------------
-- The Agda standard library
--
-- List scans: definitions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Scans.Base where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_; toList)
open import Function.Base using (_∘_)
open import Level using (Level)

private
  variable
    a b : Level
    A : Set a
    B : Set b


------------------------------------------------------------------------
-- Definitions

-- Scanr

module _ (f : A → B → B) where

  scanr⁺ : (e : B) → List A → List⁺ B
  scanr⁺ e []       = e ∷ []
  scanr⁺ e (x ∷ xs) = let y ∷ ys = scanr⁺ e xs in f x y ∷ y ∷ ys

  scanr : (e : B) → List A → List B
  scanr e = toList ∘ scanr⁺ e

-- Scanl

module _ (f : A → B → A) where

  scanl⁺ : A → List B → List⁺ A
  scanl⁺ e xs = e ∷ go e xs
    where
    go : A → List B → List A
    go _ []       = []
    go e (x ∷ xs) = let fex = f e x in fex ∷ go fex xs

  scanl : A → List B → List A
  scanl e = toList ∘ scanl⁺ e
