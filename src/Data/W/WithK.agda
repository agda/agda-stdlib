------------------------------------------------------------------------
-- The Agda standard library
--
-- Some code related to the W type that relies on the K rule
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.W.WithK where

open import Data.Product.Base using (_,_)
open import Data.Container.Core using (Container; Shape; Position; _⇒_)
open import Data.W using (W; sup)
open import Agda.Builtin.Equality using (_≡_; refl)

module _ {s p} {C : Container s p}
         {s : Shape C} {f : Position C s → W C} where

 sup-injective₂ : ∀ {g} → sup (s , f) ≡ sup (s , g) → f ≡ g
 sup-injective₂ refl = refl
