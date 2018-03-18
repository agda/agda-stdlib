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

record Thunk^P {f} {p} {F : Size → Set f} (P : ∀ i → F i → Set p)
               (i : Size) (tf : Thunk F i) : Set p where
  coinductive
  field force : {j : Size< i} → P j (tf .force)
open Thunk^P public

record Thunk^R {f g} {r} {F : Size → Set f} {G : Size → Set g}
               (R : ∀ i → F i → G i → Set r)
               (i : Size) (tf : Thunk F i) (tg : Thunk G i) : Set r where
  coinductive
  field force : {j : Size< i} → R j (tf .force) (tg .force)
open Thunk^R public
