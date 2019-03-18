------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Properties where

import Function as F
open import Relation.Binary

open import Data.Container.Core
open import Data.Container.Relation.Binary.Equality.Setoid

module _ {s p} {C : Container s p} where

  map-identity : ∀ {x e} (X : Setoid x e) xs →
                 Eq X C (map F.id xs) xs
  map-identity X xs = refl X C

  map-compose : ∀ {x y z e} {X : Set x} {Y : Set y} (Z : Setoid z e) g (f : X → Y) xs →
                Eq Z C (map g (map f xs)) (map (g F.∘′ f) xs)
  map-compose Z g f xs = refl Z C
