------------------------------------------------------------------------
-- The Agda standard library
--
-- Level polymorphic Empty type
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Empty.Polymorphic where

import Data.Empty as Empty using (⊥; ⊥-elim)
open import Level using (Level; Lift; _⊔_)

⊥ : {ℓ : Level} → Set ℓ
⊥ {ℓ} = Lift ℓ Empty.⊥

-- make ⊥-elim dependent too, as it does seem useful
⊥-elim : ∀ {w ℓ} {Whatever : ⊥ {ℓ} → Set w} → (witness : ⊥ {ℓ}) → Whatever witness
⊥-elim ()
