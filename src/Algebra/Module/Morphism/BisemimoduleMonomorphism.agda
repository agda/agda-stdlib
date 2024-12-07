------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between bisemimodules
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

open import Algebra.Module.Bundles.Raw
open import Algebra.Module.Morphism.Structures

module Algebra.Module.Morphism.BisemimoduleMonomorphism
  {r s a b ℓ₁ ℓ₂} {R : Set r} {S : Set s} {M : RawBisemimodule R S a ℓ₁} {N : RawBisemimodule R S b ℓ₂} {⟦_⟧}
  (isBisemimoduleMonomorphism : IsBisemimoduleMonomorphism M N ⟦_⟧)
  where

open IsBisemimoduleMonomorphism isBisemimoduleMonomorphism
private
  module M = RawBisemimodule M
  module N = RawBisemimodule N

open import Algebra.Bundles
open import Algebra.Core
import Algebra.Module.Definitions.Bi as BiDefs
import Algebra.Module.Definitions.Left as LeftDefs
import Algebra.Module.Definitions.Right as RightDefs
open import Algebra.Module.Structures
open import Algebra.Structures
open import Function.Base
open import Relation.Binary.Core
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

------------------------------------------------------------------------
-- Re-exports

open import Algebra.Morphism.MonoidMonomorphism
  +ᴹ-isMonoidMonomorphism public
    using ()
    renaming
      ( cong to +ᴹ-cong
      ; assoc to +ᴹ-assoc
      ; comm to +ᴹ-comm
      ; identityˡ to +ᴹ-identityˡ
      ; identityʳ to +ᴹ-identityʳ
      ; identity to +ᴹ-identity
      ; isMagma to +ᴹ-isMagma
      ; isSemigroup to +ᴹ-isSemigroup
      ; isMonoid to +ᴹ-isMonoid
      ; isCommutativeMonoid to +ᴹ-isCommutativeMonoid
      )

open import Algebra.Module.Morphism.LeftSemimoduleMonomorphism
  isLeftSemimoduleMonomorphism public
  using
    ( *ₗ-cong
    ; *ₗ-zeroˡ
    ; *ₗ-distribʳ
    ; *ₗ-identityˡ
    ; *ₗ-assoc
    ; *ₗ-zeroʳ
    ; *ₗ-distribˡ
    ; isLeftSemimodule
    )

open import Algebra.Module.Morphism.RightSemimoduleMonomorphism
  isRightSemimoduleMonomorphism public
  using
    ( *ᵣ-cong
    ; *ᵣ-zeroʳ
    ; *ᵣ-distribˡ
    ; *ᵣ-identityʳ
    ; *ᵣ-assoc
    ; *ᵣ-zeroˡ
    ; *ᵣ-distribʳ
    ; isRightSemimodule
    )

------------------------------------------------------------------------
-- Properties

module _ (+ᴹ-isMagma : IsMagma N._≈ᴹ_ N._+ᴹ_) where

  open IsMagma +ᴹ-isMagma
    using (setoid)
    renaming (∙-cong to +ᴹ-cong)
  open SetoidReasoning setoid

  private
    module MDefs = BiDefs R S M._≈ᴹ_
    module NDefs = BiDefs R S N._≈ᴹ_
    module LDefs = LeftDefs R N._≈ᴹ_
    module RDefs = RightDefs S N._≈ᴹ_

  *ₗ-*ᵣ-assoc
    : LDefs.LeftCongruent N._*ₗ_ → RDefs.RightCongruent N._*ᵣ_
    → NDefs.Associative N._*ₗ_ N._*ᵣ_
    → MDefs.Associative M._*ₗ_ M._*ᵣ_
  *ₗ-*ᵣ-assoc *ₗ-congˡ *ᵣ-congʳ *ₗ-*ᵣ-assoc x m y = injective $ begin
    ⟦ (x M.*ₗ m) M.*ᵣ y ⟧ ≈⟨ *ᵣ-homo y (x M.*ₗ m) ⟩
    ⟦ x M.*ₗ m ⟧ N.*ᵣ y   ≈⟨ *ᵣ-congʳ (*ₗ-homo x m) ⟩
    (x N.*ₗ ⟦ m ⟧) N.*ᵣ y ≈⟨ *ₗ-*ᵣ-assoc x ⟦ m ⟧ y ⟩
    x N.*ₗ (⟦ m ⟧ N.*ᵣ y) ≈˘⟨ *ₗ-congˡ (*ᵣ-homo y m) ⟩
    x N.*ₗ ⟦ m M.*ᵣ y ⟧   ≈˘⟨ *ₗ-homo x (m M.*ᵣ y) ⟩
    ⟦ x M.*ₗ (m M.*ᵣ y) ⟧ ∎

------------------------------------------------------------------------
-- Structures

module _
  {ℓr} {_≈r_ : Rel R ℓr} {_+r_ _*r_ 0r 1r}
  {ℓs} {_≈s_ : Rel S ℓs} {_+s_ _*s_ 0s 1s}
  (R-isSemiring : IsSemiring _≈r_ _+r_ _*r_ 0r 1r)
  (S-isSemiring : IsSemiring _≈s_ _+s_ _*s_ 0s 1s)
  where

  private
    R-semiring : Semiring _ _
    R-semiring = record { isSemiring = R-isSemiring }

    S-semiring : Semiring _ _
    S-semiring = record { isSemiring = S-isSemiring }

  isBisemimodule
    : IsBisemimodule R-semiring S-semiring N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N._*ₗ_ N._*ᵣ_
    → IsBisemimodule R-semiring S-semiring M._≈ᴹ_ M._+ᴹ_ M.0ᴹ M._*ₗ_ M._*ᵣ_
  isBisemimodule isBisemimodule = record
    { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid NN.+ᴹ-isCommutativeMonoid
    ; isPreleftSemimodule = record
      { *ₗ-cong = *ₗ-cong NN.+ᴹ-isMagma NN.*ₗ-cong
      ; *ₗ-zeroˡ = *ₗ-zeroˡ NN.+ᴹ-isMagma NN.*ₗ-zeroˡ
      ; *ₗ-distribʳ = *ₗ-distribʳ NN.+ᴹ-isMagma NN.*ₗ-distribʳ
      ; *ₗ-identityˡ = *ₗ-identityˡ NN.+ᴹ-isMagma NN.*ₗ-identityˡ
      ; *ₗ-assoc = *ₗ-assoc NN.+ᴹ-isMagma NN.*ₗ-congˡ NN.*ₗ-assoc
      ; *ₗ-zeroʳ = *ₗ-zeroʳ NN.+ᴹ-isMagma NN.*ₗ-congˡ NN.*ₗ-zeroʳ
      ; *ₗ-distribˡ = *ₗ-distribˡ NN.+ᴹ-isMagma NN.*ₗ-congˡ NN.*ₗ-distribˡ
      }
    ; isPrerightSemimodule = record
      { *ᵣ-cong = *ᵣ-cong NN.+ᴹ-isMagma NN.*ᵣ-cong
      ; *ᵣ-zeroʳ = *ᵣ-zeroʳ NN.+ᴹ-isMagma NN.*ᵣ-zeroʳ
      ; *ᵣ-distribˡ = *ᵣ-distribˡ NN.+ᴹ-isMagma NN.*ᵣ-distribˡ
      ; *ᵣ-identityʳ = *ᵣ-identityʳ NN.+ᴹ-isMagma NN.*ᵣ-identityʳ
      ; *ᵣ-assoc = *ᵣ-assoc NN.+ᴹ-isMagma NN.*ᵣ-congʳ NN.*ᵣ-assoc
      ; *ᵣ-zeroˡ = *ᵣ-zeroˡ NN.+ᴹ-isMagma NN.*ᵣ-congʳ NN.*ᵣ-zeroˡ
      ; *ᵣ-distribʳ = *ᵣ-distribʳ NN.+ᴹ-isMagma NN.*ᵣ-congʳ NN.*ᵣ-distribʳ
      }
    ; *ₗ-*ᵣ-assoc = *ₗ-*ᵣ-assoc NN.+ᴹ-isMagma NN.*ₗ-congˡ NN.*ᵣ-congʳ NN.*ₗ-*ᵣ-assoc
    }
    where
      module NN = IsBisemimodule isBisemimodule
