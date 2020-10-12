------------------------------------------------------------------------
-- The Agda standard library
--
-- Some items and theory for Magma
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra using (Magma)
open import Algebra.Definitions using (LeftQuotient)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (¬_)

module Algebra.Properties.Magma {a ℓ} (M : Magma a ℓ) where

open Magma M

------------------------------------------------------------------------
-- The divisibility relation:
-- x ∣ y  denotes  x divides y  as  y ≈ q ∙ x  for some q.

_∣_ : Rel Carrier (a ⊔ ℓ)
x ∣ y =  LeftQuotient _≈_ _∙_ y x

_∤_ : Rel Carrier (a ⊔ ℓ)
_∤_ x = ¬_ ∘ _∣_ x
