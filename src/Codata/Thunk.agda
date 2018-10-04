------------------------------------------------------------------------
-- The Agda standard library
--
-- The Thunk wrappers for sized codata, copredicates and corelations
------------------------------------------------------------------------

module Codata.Thunk where

open import Size

record Thunk {ℓ} (F : Size → Set ℓ) (i : Size) : Set ℓ where
  coinductive
  field force : {j : Size< i} → F j
open Thunk public

Thunk^P : ∀ {f p} {F : Size → Set f} (P : Size → F ∞ → Set p)
          (i : Size) (tf : Thunk F ∞) → Set p
Thunk^P P i tf = Thunk (λ i → P i (tf .force)) i

Thunk^R : ∀ {f g r} {F : Size → Set f} {G : Size → Set g}
          (R : Size → F ∞ → G ∞ → Set r)
          (i : Size) (tf : Thunk F ∞) (tg : Thunk G ∞) → Set r
Thunk^R R i tf tg = Thunk (λ i → R i (tf .force) (tg .force)) i

