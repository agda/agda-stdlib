------------------------------------------------------------------------
-- The Agda standard library
--
-- Induction over Subset
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Fin.Subset.Induction where

open import Data.Nat.Base using (ℕ)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Fin.Subset using (Subset; _⊂_; ∣_∣)
open import Data.Fin.Subset.Properties
open import Induction
open import Induction.WellFounded as WF

------------------------------------------------------------------------
-- Re-export accessability

open WF public using (Acc; acc)

------------------------------------------------------------------------
-- Complete induction based on _⊂_

⊂-Rec : ∀ {n ℓ} → RecStruct (Subset n) ℓ ℓ
⊂-Rec = WfRec _⊂_

⊂-wellFounded : ∀ {n} → WellFounded (_⊂_ {n})
⊂-wellFounded {n} = Subrelation.wellFounded p⊂q⇒∣p∣<∣q∣ (InverseImage.wellFounded ∣_∣ <-wellFounded)
