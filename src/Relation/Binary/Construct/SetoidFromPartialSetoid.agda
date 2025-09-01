------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of a PartialSetoid into a Setoid
------------------------------------------------------------------------

open import Relation.Binary.Bundles using (PartialSetoid; Setoid)

module Relation.Binary.Construct.SetoidFromPartialSetoid
  {a ℓ} (S : PartialSetoid a ℓ) where

open import Function.Base using (id; _on_)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures
  using (IsEquivalence)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism)

private
  module S = PartialSetoid S


------------------------------------------------------------------------
-- Definitions

record Carrier : Set (a ⊔ ℓ) where

  field
    ι    : S.Carrier
    refl : ι S.≈ ι

open Carrier public using (ι)

_≈_ : Rel Carrier _
_≈_ = S._≈_ on ι

-- Structure

isEquivalence : IsEquivalence _≈_
isEquivalence = record
  { refl = λ {x = x} → Carrier.refl x
  ; sym = S.sym
  ; trans = S.trans
  }

-- Bundle

setoid : Setoid _ _
setoid = record { isEquivalence = isEquivalence }

-- Monomorphism

isRelHomomorphism : IsRelHomomorphism _≈_ S._≈_ ι
isRelHomomorphism = record { cong = id }

isRelMonomorphism : IsRelMonomorphism _≈_ S._≈_ ι
isRelMonomorphism = record { isHomomorphism = isRelHomomorphism ; injective = id }
