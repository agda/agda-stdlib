------------------------------------------------------------------------
-- The Agda standard library
--
-- Conversion of a PartialSetoid into a Setoid
------------------------------------------------------------------------

open import Relation.Binary.Bundles using (PartialSetoid; Setoid)

module Relation.Binary.Construct.SetoidFromPartialSetoid
  {a ℓ} (S : PartialSetoid a ℓ) where

open import Data.Product.Base using (_,_; Σ; proj₁)
open import Function.Base using (id)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive)
open import Relation.Binary.Structures
  using (IsPartialEquivalence; IsEquivalence)
open import Relation.Binary.Morphism.Structures
  using (IsRelHomomorphism; IsRelMonomorphism)

private
  module S = PartialSetoid S

  variable
    x y z : S.Carrier

------------------------------------------------------------------------
-- Definitions

Carrier : Set _
Carrier = Σ S.Carrier λ x → x S.≈ x

_≈_ : Rel Carrier _
x≈x@(x , _) ≈ y≈y@(y , _) = x S.≈ y

-- Properties

refl : Reflexive _≈_
refl {x = _ , x≈x} = x≈x

-- Structure

isEquivalence : IsEquivalence _≈_
isEquivalence = record
  { refl = λ {x} → refl {x = x}
  ; sym = S.sym
  ; trans = S.trans
  }

-- Bundle

setoid : Setoid _ _
setoid = record { isEquivalence = isEquivalence }

-- Monomorphism

isRelHomomorphism : IsRelHomomorphism _≈_ S._≈_ proj₁
isRelHomomorphism = record { cong = id }

isRelMonomorphism : IsRelMonomorphism _≈_ S._≈_ proj₁
isRelMonomorphism = record { isHomomorphism = isRelHomomorphism ; injective = id }
