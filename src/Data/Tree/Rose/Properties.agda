------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of rose trees
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --sized-types #-}

module Data.Tree.Rose.Properties where

open import Level using (Level)
open import Size
open import Data.List.Base as List using (List)
open import Data.List.Extrema.Nat using (max)
import Data.List.Properties as List
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Tree.Rose using (Rose; node; map; depth; foldr)
open import Function.Base using (_∘′_; _$_; _∘_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≗_; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open ≡-Reasoning

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c
    i : Size

------------------------------------------------------------------------
-- map properties

map-∘ : (f : A → B) (g : B → C) →
              map {i = i} (g ∘′ f) ≗ map {i = i} g ∘′ map {i = i} f
map-∘ f g (node a ts) = cong (node (g (f a))) $ begin
  List.map (map (g ∘′ f)) ts             ≡⟨ List.map-cong (map-∘ f g) ts ⟩
  List.map (map g ∘ map f) ts            ≡⟨ List.map-∘ ts ⟩
  List.map (map g) (List.map (map f) ts) ∎

depth-map : (f : A → B) (t : Rose A i) → depth {i = i} (map {i = i} f t) ≡ depth {i = i} t
depth-map f (node a ts) = cong (suc ∘′ max 0) $ begin
  List.map depth (List.map (map f) ts) ≡⟨ List.map-∘ ts ⟨
  List.map (depth ∘′ map f) ts         ≡⟨ List.map-cong (depth-map f) ts ⟩
  List.map depth ts ∎

------------------------------------------------------------------------
-- foldr properties

foldr-map : (f : A → B) (n : B → List C → C) (ts : Rose A i) →
            foldr {i = i} n (map {i = i} f ts) ≡ foldr {i = i} (n ∘′ f) ts
foldr-map f n (node a ts) = cong (n (f a)) $ begin
  List.map (foldr n) (List.map (map f) ts) ≡⟨ List.map-∘ ts ⟨
  List.map (foldr n ∘′ map f) ts           ≡⟨ List.map-cong (foldr-map f n) ts ⟩
  List.map (foldr (n ∘′ f)) ts             ∎

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

map-compose = map-∘
{-# WARNING_ON_USAGE map-compose
"Warning: map-compose was deprecated in v2.0.
Please use map-∘ instead."
#-}
