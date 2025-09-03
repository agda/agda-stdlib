------------------------------------------------------------------------
-- The Agda standard library
--
-- Equaliser of a kernel pair in Setoid
------------------------------------------------------------------------

open import Relation.Binary.Bundles using (PartialSetoid; Setoid)

module Relation.Binary.Construct.Kernel
  {a i ℓ} {I : Set i}
  (S : PartialSetoid a ℓ) (let module S = PartialSetoid S)
  (f g : I → S.Carrier)
  where

open import Function.Base using (id; _∘_; _on_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Defined)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism)

import Relation.Binary.Properties.PartialSetoid S as Properties


------------------------------------------------------------------------
-- Definitions

record Carrier : Set (a ⊔ i ⊔ ℓ) where

  field
    h    : I
    refl : (f h) S.≈ (g h)

  ι : S.Carrier
  ι = f h


open Carrier public using (ι)

_≈_ : Rel Carrier _
_≈_ = S._≈_ on ι

-- Structure

isEquivalence : IsEquivalence _≈_
isEquivalence = record
  { refl = λ {x = x} → Properties.partial-reflˡ (Carrier.refl x)
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

