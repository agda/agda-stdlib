------------------------------------------------------------------------
-- The Agda standard library
--
-- List scans: definition and properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Scans where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.NonEmpty.Base as List⁺ using (List⁺; _∷_; toList)
import Data.List.Properties as List
import Data.List.NonEmpty.Properties as List⁺
open import Function.Base using (_∘_; _$_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≗_; refl; trans; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties using (module ≡-Reasoning)

private
  variable
    a b : Level
    A : Set a
    B : Set b


------------------------------------------------------------------------
-- Definitions

-- Inits

inits⁺ : List A → List⁺ (List A)
inits⁺ xs = [] ∷ go xs
  where
  go : List A → List (List A)
  go []       = []
  go (x ∷ xs) = List.[ x ] ∷ List.map (x ∷_) (go xs)

-- Tails

tails⁺ : List A → List⁺ (List A)
tails⁺ xs = xs ∷ go xs
  where
  go : List A → List (List A)
  go []       = []
  go (x ∷ xs) = xs ∷ go xs

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

------------------------------------------------------------------------
-- Properties

-- inits

toList-inits⁺ : toList ∘ inits⁺ ≗ List.inits {A = A}
toList-inits⁺ []       = refl
toList-inits⁺ (x ∷ xs) = cong (([] ∷_) ∘ List.map (x ∷_)) (toList-inits⁺ xs)

-- tails

toList-tails⁺ : toList ∘ tails⁺ ≗ List.tails {A = A}
toList-tails⁺ []          = refl
toList-tails⁺ ys@(_ ∷ xs) = cong (ys ∷_) (toList-tails⁺ xs)

-- scanr⁺ and scanr

module _ (f : A → B → B) (e : B) where

  private
    h = List.foldr f e

  scanr⁺-defn : scanr⁺ f e ≗ List⁺.map h ∘ tails⁺
  scanr⁺-defn []       = refl
  scanr⁺-defn (x ∷ xs) = let eq = scanr⁺-defn xs
    in cong₂ (λ z → f x z ∷_) (cong List⁺.head eq) (cong toList eq)

  scanr-defn : scanr f e ≗ List.map h ∘ List.tails
  scanr-defn xs = begin
    scanr f e xs
      ≡⟨ cong toList (scanr⁺-defn xs) ⟩
    toList (List⁺.map h (tails⁺ xs))
      ≡⟨⟩
    List.map h (toList (tails⁺ xs))
      ≡⟨ cong (List.map h) (toList-tails⁺ xs) ⟩
    List.map h (List.tails xs)
      ∎
    where open ≡-Reasoning

-- scanl⁺ and scanl

module _ (f : A → B → A) where

  private
    h = List.foldl f

  scanl⁺-defn : ∀ e → scanl⁺ f e ≗ List⁺.map (h e) ∘ inits⁺
  scanl⁺-defn e []       = refl
  scanl⁺-defn e (x ∷ xs) = let eq = scanl⁺-defn (f e x) xs in
    cong (e ∷_) $ cong (f e x ∷_) $ trans (cong List⁺.tail eq) (List.map-∘ _)

  scanl-defn : ∀ e → scanl f e ≗ List.map (h e) ∘ List.inits
  scanl-defn e []       = refl
  scanl-defn e (x ∷ xs) = cong (e ∷_) $ begin
    scanl f (f e x) xs
      ≡⟨ scanl-defn (f e x) xs ⟩
    List.map (h (f e x)) (List.inits xs)
      ≡⟨⟩
    List.map (h e ∘ (x ∷_)) (List.inits xs)
      ≡⟨ List.map-∘ (List.inits xs) ⟩
    List.map (h e) (List.map (x ∷_) (List.inits xs))
     ∎
    where open ≡-Reasoning
