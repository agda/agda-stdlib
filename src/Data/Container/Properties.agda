------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on containers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Properties where

open import Data.Container.Core using (Container; map)
open import Data.Container.Relation.Binary.Equality.Setoid using (Eq; refl)
import Function.Base as F using (id; _∘′_)
open import Relation.Binary.Bundles using (Setoid)

module _ {s p} {C : Container s p} where

  map-identity : ∀ {x e} (X : Setoid x e) xs →
                 Eq X C (map F.id xs) xs
  map-identity X xs = refl X C

  map-compose : ∀ {x y z e} {X : Set x} {Y : Set y} (Z : Setoid z e) g (f : X → Y) xs →
                Eq Z C (map g (map f xs)) (map (g F.∘′ f) xs)
  map-compose Z g f xs = refl Z C
