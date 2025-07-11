------------------------------------------------------------------------
-- The Agda standard library
--
-- Some theory for Semigroup
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Algebra.Core using (Op₂)
open import Algebra.Structures.IsMagma using (IsMagma)

module Algebra.Properties.IsMagma
  {a ℓ} {A} {_≈_} {_∙_} (isMagma : IsMagma {a = a} {ℓ = ℓ} {A = A} _≈_ _∙_)
  where

open import Algebra.Definitions _≈_
  using (Alternative; LeftAlternative; RightAlternative; Flexible)
open import Data.Product.Base using (_,_)

open IsMagma isMagma
  using (setoid; trans ; refl; sym; ∙-cong; ∙-congˡ; ∙-congʳ)
