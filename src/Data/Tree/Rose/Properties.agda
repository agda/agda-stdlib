------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe --sized-types #-}

module Data.Tree.Rose.Properties where

open import Level using (Level)
open import Size
open import Data.List.Base as List using (List)
open import Data.List.Extrema.Nat
import Data.List.Properties as Listₚ
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Tree.Rose
open import Function.Base
open import Relation.Binary.PropositionalEquality
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

map-compose : (f : A → B) (g : B → C) →
              map {i = i} (g ∘′ f) ≗ map {i = i} g ∘′ map {i = i} f
map-compose f g (node a ts) = cong (node (g (f a))) $ begin
  List.map (map (g ∘′ f)) ts             ≡⟨ Listₚ.map-cong (map-compose f g) ts ⟩
  List.map (map g ∘ map f) ts            ≡⟨ Listₚ.map-compose ts ⟩
  List.map (map g) (List.map (map f) ts) ∎

depth-map : (f : A → B) (t : Rose A i) → depth {i = i} (map {i = i} f t) ≡ depth {i = i} t
depth-map f (node a ts) = cong (suc ∘′ max 0) $ begin
  List.map depth (List.map (map f) ts) ≡˘⟨ Listₚ.map-compose ts ⟩
  List.map (depth ∘′ map f) ts         ≡⟨ Listₚ.map-cong (depth-map f) ts ⟩
  List.map depth ts ∎

------------------------------------------------------------------------
-- foldr properties

foldr-map : (f : A → B) (n : B → List C → C) (ts : Rose A i) →
            foldr {i = i} n (map {i = i} f ts) ≡ foldr {i = i} (n ∘′ f) ts
foldr-map f n (node a ts) = cong (n (f a)) $ begin
  List.map (foldr n) (List.map (map f) ts) ≡˘⟨ Listₚ.map-compose ts ⟩
  List.map (foldr n ∘′ map f) ts           ≡⟨ Listₚ.map-cong (foldr-map f n) ts ⟩
  List.map (foldr (n ∘′ f)) ts             ∎
