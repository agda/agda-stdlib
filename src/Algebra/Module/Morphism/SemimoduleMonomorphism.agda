------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of a monomorphism between semimodules
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Module.Bundles.Raw
open import Algebra.Module.Morphism.Structures

module Algebra.Module.Morphism.SemimoduleMonomorphism
  {r a b ℓ₁ ℓ₂} {R : Set r} {M : RawSemimodule R a ℓ₁} {N : RawSemimodule R b ℓ₂} {⟦_⟧}
  (isSemimoduleMonomorphism : IsSemimoduleMonomorphism M N ⟦_⟧)
  where

open IsSemimoduleMonomorphism isSemimoduleMonomorphism
private
  module M = RawSemimodule M
  module N = RawSemimodule N

open import Algebra.Bundles
open import Algebra.Core
import Algebra.Module.Definitions.Bi.Simultaneous as SimulDefs
open import Algebra.Module.Structures
open import Algebra.Structures
open import Function.Base
open import Relation.Binary.Core
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- Re-exports

open import Algebra.Module.Morphism.BisemimoduleMonomorphism isBisemimoduleMonomorphism public

------------------------------------------------------------------------
-- Properties

module _ (+ᴹ-isMagma : IsMagma N._≈ᴹ_ N._+ᴹ_) where
  open IsMagma +ᴹ-isMagma
    using (setoid)
    renaming (∙-cong to +ᴹ-cong)
  open SetoidReasoning setoid

  private
    module MDefs = SimulDefs R M._≈ᴹ_
    module NDefs = SimulDefs R N._≈ᴹ_

  *ₗ-*ᵣ-coincident : NDefs.Coincident N._*ₗ_ N._*ᵣ_ → MDefs.Coincident M._*ₗ_ M._*ᵣ_
  *ₗ-*ᵣ-coincident *ₗ-*ᵣ-coincident x m = injective $ begin
    ⟦ x M.*ₗ m ⟧ ≈⟨ *ₗ-homo x m ⟩
    x N.*ₗ ⟦ m ⟧ ≈⟨ *ₗ-*ᵣ-coincident x ⟦ m ⟧ ⟩
    ⟦ m ⟧ N.*ᵣ x ≈˘⟨ *ᵣ-homo x m ⟩
    ⟦ m M.*ᵣ x ⟧ ∎

------------------------------------------------------------------------
-- Structures

module _ {ℓr} {_≈_ : Rel R ℓr} {_+_ _*_ 0# 1#} (R-isCommutativeSemiring : IsCommutativeSemiring _≈_ _+_ _*_ 0# 1#) where

  private
    R-commutativeSemiring : CommutativeSemiring _ _
    R-commutativeSemiring = record { isCommutativeSemiring = R-isCommutativeSemiring }

  open IsCommutativeSemiring R-isCommutativeSemiring

  isSemimodule
    : IsSemimodule R-commutativeSemiring N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N._*ₗ_ N._*ᵣ_
    → IsSemimodule R-commutativeSemiring M._≈ᴹ_ M._+ᴹ_ M.0ᴹ M._*ₗ_ M._*ᵣ_
  isSemimodule isSemimodule = record
    { isBisemimodule = isBisemimodule isSemiring isSemiring NN.isBisemimodule
    ; *ₗ-*ᵣ-coincident = *ₗ-*ᵣ-coincident NN.+ᴹ-isMagma NN.*ₗ-*ᵣ-coincident
    }
    where
      module NN = IsSemimodule isSemimodule
