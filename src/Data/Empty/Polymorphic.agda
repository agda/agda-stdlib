------------------------------------------------------------------------
-- The Agda standard library
--
-- Level polymorphic Empty type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Empty.Polymorphic where

import Data.Empty as ⊥
open import Level

⊥ : {ℓ : Level} → Set ℓ
⊥ {ℓ} = Lift ℓ ⊥.⊥

-- make ⊥-elim-P dependent too, as it does seem useful
⊥-elim-P : ∀ {w ℓ} {Whatever : ⊥ {ℓ} → Set w} → (witness : ⊥ {ℓ}) → Whatever witness
⊥-elim-P ()
