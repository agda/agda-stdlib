------------------------------------------------------------------------
-- The Agda standard library
--
-- M-types (the dual of W-types)
------------------------------------------------------------------------

module Codata.Musical.M where

open import Codata.Musical.Notation
open import Level
open import Data.Product hiding (map)
open import Data.Container.Core

-- The family of M-types.

data M {s p} (C : Container s p) : Set (s ⊔ p) where
  inf : ⟦ C ⟧ (∞ (M C)) → M C

-- Projections.

module _ {s p} (C : Container s p) (open Container C) where

  head : M C → Shape
  head (inf (x , _)) = x

  tail : (x : M C) → Position (head x) → M C
  tail (inf (x , f)) b = ♭ (f b)

-- map

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         (m : C₁ ⇒ C₂) where

  map : M C₁ → M C₂
  map (inf (x , f)) = inf (shape m x , λ p → ♯ map (♭ (f (position m p))))


-- unfold

module _ {s p ℓ} {C : Container s p} (open Container C)
         {S : Set ℓ} (alg : S → ⟦ C ⟧ S) where

  unfold : S → M C
  unfold seed = let (x , f) = alg seed in
                inf (x , λ p → ♯ unfold (f p))
