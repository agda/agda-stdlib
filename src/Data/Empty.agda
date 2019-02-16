------------------------------------------------------------------------
-- The Agda standard library
--
-- Empty type
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Empty where

open import Level

data ⊥ : Set where

{-# FOREIGN GHC data AgdaEmpty #-}
{-# COMPILE GHC ⊥ = data MAlonzo.Code.Data.Empty.AgdaEmpty () #-}

⊥-elim : ∀ {w} {Whatever : Set w} → ⊥ → Whatever
⊥-elim ()
