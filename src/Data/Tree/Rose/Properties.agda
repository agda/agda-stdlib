------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of rose trees
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Tree.Rose.Properties where

open import Level using (Level)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Extrema.Nat using (max)
import Data.List.Properties as List
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Tree.Rose
  using (Rose; node; map; module Map; foldr; module Foldr; depth)
open import Function.Base using (const; _∘′_; _$_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; _≗_; cong; cong₂)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c


------------------------------------------------------------------------
-- map properties

module _ (f : A → B) (open Map) where

  mapList≗MapMap : mapList f ≗ List.map (map f)
  mapList≗MapMap []       = refl
  mapList≗MapMap (t ∷ ts) = cong (map f t ∷_) (mapList≗MapMap ts)

module _ (f : A → B) (g : B → C) (open Map) where

  map-∘ : map (g ∘′ f) ≗ map g ∘′ map f
  map-∘ (node a ts) = cong (node (g (f a))) $ begin
    mapList (g ∘′ f) ts                    ≡⟨ mapList≗MapMap (g ∘′ f) ts ⟩
    List.map (map (g ∘′ f)) ts             ≡⟨ map-cong ts ⟩
    List.map (map g ∘′ map f) ts           ≡⟨ List.map-∘ ts ⟩
    List.map (map g) (List.map (map f) ts) ≡⟨ mapList≗MapMap g _ ⟨
    mapList g (List.map (map f) ts)        ≡⟨ cong (mapList g) (mapList≗MapMap f ts) ⟨
    mapList g (mapList f ts)               ∎
    where
    open ≡-Reasoning
    map-cong : List.map (map (g ∘′ f)) ≗ List.map (map g ∘′ map f)
    map-cong []       = refl
    map-cong (t ∷ ts) = cong₂ _∷_ (map-∘ t) (map-cong ts)

------------------------------------------------------------------------
-- foldr properties

module _ (n : A → List B → B) (open Foldr) where

  foldrList≗MapFoldr : foldrList n ≗ List.map (foldr n)
  foldrList≗MapFoldr []       = refl
  foldrList≗MapFoldr (t ∷ ts) = cong (foldr n t ∷_) (foldrList≗MapFoldr ts)

module _ (f : A → B) where

  module _ (n : B → List C → C) (open Foldr) (open Map) where

    foldr-map : foldr n ∘′ map f ≗ foldr (n ∘′ f)
    foldr-map (node a ts) = cong (n (f a)) $ begin
      foldrList n (mapList f ts)               ≡⟨ cong (foldrList n) (mapList≗MapMap f ts) ⟩
      foldrList n (List.map (map f) ts)        ≡⟨ foldrList≗MapFoldr n _ ⟩
      List.map (foldr n) (List.map (map f) ts) ≡⟨ List.map-∘ ts ⟨
      List.map (foldr n ∘′ map f) ts           ≡⟨ foldr-map-cong ts ⟩
      List.map (foldr (n ∘′ f)) ts             ≡⟨ foldrList≗MapFoldr (n ∘′ f) ts ⟨
      foldrList (n ∘′ f) ts ∎
      where
      open ≡-Reasoning
      foldr-map-cong : List.map (foldr n ∘′ map f) ≗ List.map (foldr (n ∘′ f))
      foldr-map-cong []       = refl
      foldr-map-cong (t ∷ ts) = cong₂ _∷_ (foldr-map t) (foldr-map-cong ts)

  depth-map : depth ∘′ map f ≗ depth
  depth-map = foldr-map $ const (suc ∘′ max zero)
