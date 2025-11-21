------------------------------------------------------------------------
-- The Agda standard library
--
-- Definition of the centre as a subtype of (the carrier of) a raw magma
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Core using (Op₂)
open import Relation.Binary.Core using (Rel)

module Algebra.Construct.Centre.Center
  {c ℓ} {Carrier : Set c} (_∼_ : Rel Carrier ℓ) (_∙_ : Op₂ Carrier)
  where

open import Algebra.Definitions _∼_ using (Central)
open import Function.Base using (id; _on_)
open import Level using (_⊔_)
import Relation.Binary.Morphism.Construct.On as On


------------------------------------------------------------------------
-- Definitions

record Center : Set (c ⊔ ℓ) where
  field
    ι       : Carrier
    central : Central _∙_ ι

open Center public
  using (ι)

∙-comm : ∀ g h → (ι g ∙ ι h) ∼ (ι h ∙ ι g)
∙-comm g h = Center.central g (ι h)

-- Center as subtype of Carrier

open On _∼_ ι public
  using (_≈_; isRelHomomorphism; isRelMonomorphism)
