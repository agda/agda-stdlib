------------------------------------------------------------------------
-- The Agda standard library
--
-- Construct IsXHomomorphisms from a function which is homomorphic
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Morphism.Construct.On
  where

open import Algebra.Bundles.Raw
open import Algebra.Core using (Op₁; Op₂)
import Algebra.Morphism.Definitions as MorphismDefinitions
  --using (Homomorphic₁; Homomorphic₂)
open import Algebra.Morphism.Structures
  --using (IsMagmaHomomorphism; IsMagmaMonomorphism)
open import Level using (Level)
import Relation.Binary.Morphism.Construct.On as On
  using (_≈_; module ι)

private
  variable
    a b ℓ : Level
    A : Set a
    _∙_ : Op₂ A
    ε   : A
    _⁻¹ : Op₁ A

------------------------------------------------------------------------
-- Definitions

module Magma
         (rawMagma : RawMagma b ℓ) (let module B = RawMagma rawMagma)
         (open MorphismDefinitions A _ B._≈_) (f : A → B.Carrier)
         (∙-homo : Homomorphic₂ f _∙_ B._∙_)
         where

  open On B._≈_ f using (_≈_; module ι)

  private
    rawMagmaOn : RawMagma _ _
    rawMagmaOn = record { _≈_ = _≈_ ; _∙_ = _∙_ }

  isMagmaHomomorphism : IsMagmaHomomorphism rawMagmaOn rawMagma f
  isMagmaHomomorphism = record
    { isRelHomomorphism = ι.isHomomorphism
    ; homo = ∙-homo
    }

  isMagmaMonomorphism : IsMagmaMonomorphism rawMagmaOn rawMagma f
  isMagmaMonomorphism = record
    { isMagmaHomomorphism = isMagmaHomomorphism
    ; injective = ι.injective
    }

module Monoid
         (rawMonoid : RawMonoid b ℓ) (let module B = RawMonoid rawMonoid)
         (open MorphismDefinitions A _ B._≈_) (f : A → B.Carrier)
         (∙-homo : Homomorphic₂ f _∙_ B._∙_) (ε-homo : Homomorphic₀ f ε B.ε)
         where

  open On B._≈_ f using (_≈_; module ι)

  private
    rawMonoidOn : RawMonoid _ _
    rawMonoidOn = record { _≈_ = _≈_ ; _∙_ = _∙_ ; ε = ε }

  isMonoidHomomorphism : IsMonoidHomomorphism rawMonoidOn rawMonoid f
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = Magma.isMagmaHomomorphism B.rawMagma f ∙-homo
    ; ε-homo = ε-homo
    }

  isMonoidMonomorphism : IsMonoidMonomorphism rawMonoidOn rawMonoid f
  isMonoidMonomorphism = record
    { isMonoidHomomorphism = isMonoidHomomorphism
    ; injective = ι.injective
    }

module Group
         (rawGroup : RawGroup b ℓ) (let module B = RawGroup rawGroup)
         (open MorphismDefinitions A _ B._≈_) (f : A → B.Carrier)
         (∙-homo : Homomorphic₂ f _∙_ B._∙_) (ε-homo : Homomorphic₀ f ε B.ε)
         (⁻¹-homo : Homomorphic₁ f _⁻¹ B._⁻¹)
         where

  open On B._≈_ f using (_≈_; module ι)

  private
    rawGroupOn : RawGroup _ _
    rawGroupOn = record { _≈_ = _≈_ ; _∙_ = _∙_ ; ε = ε; _⁻¹ = _⁻¹ }

  isGroupHomomorphism : IsGroupHomomorphism rawGroupOn rawGroup f
  isGroupHomomorphism = record
    { isMonoidHomomorphism = Monoid.isMonoidHomomorphism B.rawMonoid f ∙-homo ε-homo
    ; ⁻¹-homo = ⁻¹-homo
    }

  isGroupMonomorphism : IsGroupMonomorphism rawGroupOn rawGroup f
  isGroupMonomorphism = record
    { isGroupHomomorphism = isGroupHomomorphism
    ; injective = ι.injective
    }

{- etc. -}
