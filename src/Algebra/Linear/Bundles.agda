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

  field
    isBasis       : IsBasis mod
    isVectorSpace : IsVectorSpace mod isBasis

  open IsBasis       isBasis       public
  open IsVectorSpace isVectorSpace public

  -- Linear maps from vectors to scalars.
  V⊸S = LinearMap mod ⟨module⟩

  -- Equivalent vector generator.
  v : V⊸S → V
  v lm = vgen (LinearMap.f lm) basisSet

  open Setoid (≈ᴸ-setoid mod ⟨module⟩) public using () renaming
    ( _≈_ to _≈ᴸ_
    ; _≉_ to _≉ᴸ_
    )

