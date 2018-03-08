------------------------------------------------------------------------
-- The Agda standard library
--
-- The Thunk wrapper used to define sized codata
------------------------------------------------------------------------

module Codata.Thunk where

open import Size

record Thunk {ℓ} (F : Size → Set ℓ) (i : Size) : Set ℓ where
  coinductive
  field force : {j : Size< i} → F j
open Thunk public
