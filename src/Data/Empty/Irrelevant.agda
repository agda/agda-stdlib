------------------------------------------------------------------------
-- The Agda standard library
--
-- An irrelevant version of ⊥-elim
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Empty.Irrelevant where

open import Data.Empty hiding (⊥-elim)

⊥-elim : ∀ {w} {Whatever : Set w} → .⊥ → Whatever
⊥-elim ()
