------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to the W type that relies on the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.W.WithK where

open import Data.Product
open import Data.Container.Core
open import Data.W
open import Agda.Builtin.Equality

module _ {s p} {C : Container s p} (open Container C)
         {s : Shape} {f : Position s → W C} where

 sup-injective₂ : ∀ {g} → sup (s , f) ≡ sup (s , g) → f ≡ g
 sup-injective₂ refl = refl
