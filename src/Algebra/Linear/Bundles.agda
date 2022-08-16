------------------------------------------------------------------------
-- The Agda standard library
--
-- Some bundles of linear algebraic structures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Linear.Bundles where

open import Algebra        using (CommutativeRing)
open import Algebra.Linear.Structures
open import Algebra.Module using (Module)
open import Algebra.Module.Construct.TensorUnit using (⟨module⟩)
open import Algebra.Module.Morphism.Bundles
open import Level          using (Level; _⊔_; suc)
open import Relation.Binary

-- Abstract vector spaces.
--
-- A "vector space" is a Module with a commutative, homomorphic inner
-- product and a complete set of building blocks for mapping the space.
record VectorSpace
  {r ℓr m ℓm : Level}
  {ring      : CommutativeRing r ℓr}
  (mod       : Module ring m ℓm)
  : Set (suc (ℓr ⊔ r ⊔ ℓm ⊔ m)) where

  constructor mkVS

  open CommutativeRing ring renaming (Carrier  to S)   public
  open Module          mod  renaming (Carrierᴹ to V)   public

  infix 7 _∙_

  field
    _∙_ : V → V → S
    isVectorSpace : IsVectorSpace mod _∙_

  open IsVectorSpace isVectorSpace public

  open Setoid (≈ᴸ-setoid mod ⟨module⟩) public using () renaming
    ( _≈_ to _≈ᴸ_
    ; _≉_ to _≉ᴸ_
    )

record Basis
  {r ℓr m ℓm   : Level}
  {ring        : CommutativeRing r ℓr}
  {mod         : Module ring m ℓm}
  (vectorSpace : VectorSpace mod)
  : Set (suc (r ⊔ m ⊔ ℓm))
  where

  constructor mkBasis

  open VectorSpace vectorSpace public

  field
    basisFor : BasisFor mod _∙_

  open BasisFor basisFor public

  -- Linear maps from vectors to scalars.
  V⊸S : Set (r ⊔ ℓr ⊔ m ⊔ ℓm)
  V⊸S = LinearMap mod ⟨module⟩

  -- Every linear map from a vector to a scalar is equivalent to a vector.
  -- (This is proved in `Isomorphism 1` in `Algebra.Linear.Properties.VectorSpace`.)
  lmToVec : V⊸S → V
  lmToVec lm = vgen (LinearMap.f lm) basisSet

