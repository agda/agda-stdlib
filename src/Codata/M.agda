------------------------------------------------------------------------
-- The Agda standard library
--
-- M-types (the dual of W-types)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Codata.M where

open import Size
open import Level
open import Codata.Thunk using (Thunk; force)
open import Data.Product hiding (map)
open import Data.Container.Core
import Data.Container as C

data M {s p} (C : Container s p) (i : Size) : Set (s ⊔ p) where
  inf : ⟦ C ⟧ (Thunk (M C) i) → M C i

module _ {s p} {C : Container s p} where

  head : ∀ {i} → M C i → Shape C
  head (inf (x , f)) = x

  tail : (x : M C ∞) → Position C (head x) → M C ∞
  tail (inf (x , f)) = λ p → f p .force

-- map

module _ {s₁ s₂ p₁ p₂} {C₁ : Container s₁ p₁} {C₂ : Container s₂ p₂}
         (m : C₁ ⇒ C₂) where

  map : ∀ {i} → M C₁ i → M C₂ i
  map (inf t) = inf (⟪ m ⟫ (C.map (λ t → λ where .force → map (t .force)) t))

-- unfold

module _ {s p ℓ} {C : Container s p} (open Container C)
         {S : Set ℓ} (alg : S → ⟦ C ⟧ S) where

  unfold : S → ∀ {i} → M C i
  unfold seed = let (x , next) = alg seed in
                inf (x , λ p → λ where .force → unfold (next p))


------------------------------------------------------------------------
-- Legacy

open import Codata.Musical.Notation using (♭; ♯_)
import Codata.Musical.M as M

module _ {s p} {C : Container s p} where

  fromMusical : ∀ {i} → M.M C → M C i
  fromMusical (M.inf t) = inf (C.map rec t) where
    rec = λ x → λ where .force → fromMusical (♭ x)

  toMusical : M C ∞ → M.M C
  toMusical (inf (s , f)) = M.inf (s , λ p → ♯ toMusical (f p .force))
