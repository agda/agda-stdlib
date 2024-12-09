------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomomorphism between right semimodules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Module.Bundles.Raw
open import Algebra.Module.Morphism.Structures

module Algebra.Module.Morphism.RightSemimoduleMonomorphism
  {r a b ℓ₁ ℓ₂} {R : Set r} {M : RawRightSemimodule R a ℓ₁} {N : RawRightSemimodule R b ℓ₂} {⟦_⟧}
  (isRightSemimoduleMonomorphism : IsRightSemimoduleMonomorphism M N ⟦_⟧)
  where

open IsRightSemimoduleMonomorphism isRightSemimoduleMonomorphism
private
  module M = RawRightSemimodule M
  module N = RawRightSemimodule N

open import Algebra.Bundles
open import Algebra.Core
import Algebra.Module.Definitions.Right as RightDefs
open import Algebra.Module.Structures
open import Algebra.Structures
open import Function.Base
open import Level
open import Relation.Binary.Core
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  variable
    ℓr : Level
    _≈_ : Rel R ℓr
    _+_ _*_ : Op₂ R
    0# 1# : R

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

------------------------------------------------------------------------
-- Properties

module _ (+ᴹ-isMagma : IsMagma N._≈ᴹ_ N._+ᴹ_) where

  open IsMagma +ᴹ-isMagma
    using (setoid)
    renaming (∙-cong to +ᴹ-cong′)
  open SetoidReasoning setoid

  module MDefs = RightDefs R M._≈ᴹ_
  module NDefs = RightDefs R N._≈ᴹ_

  *ᵣ-cong : NDefs.Congruent _≈_ N._*ᵣ_ → MDefs.Congruent _≈_ M._*ᵣ_
  *ᵣ-cong *ᵣ-cong {x} {y} {u} {v} x≈ᴹy u≈v = injective $ begin
    ⟦ x M.*ᵣ u ⟧ ≈⟨ *ᵣ-homo u x ⟩
    ⟦ x ⟧ N.*ᵣ u ≈⟨ *ᵣ-cong (⟦⟧-cong x≈ᴹy) u≈v ⟩
    ⟦ y ⟧ N.*ᵣ v ≈˘⟨ *ᵣ-homo v y ⟩
    ⟦ y M.*ᵣ v ⟧ ∎

  *ᵣ-zeroʳ : NDefs.RightZero 0# N.0ᴹ N._*ᵣ_ → MDefs.RightZero 0# M.0ᴹ M._*ᵣ_
  *ᵣ-zeroʳ {0# = 0#} *ᵣ-zeroʳ x = injective $ begin
    ⟦ x M.*ᵣ 0# ⟧ ≈⟨ *ᵣ-homo 0# x ⟩
    ⟦ x ⟧ N.*ᵣ 0# ≈⟨ *ᵣ-zeroʳ ⟦ x ⟧ ⟩
    N.0ᴹ          ≈˘⟨ 0ᴹ-homo ⟩
    ⟦ M.0ᴹ ⟧      ∎

  *ᵣ-distribˡ : N._*ᵣ_ NDefs.DistributesOverˡ _+_ ⟶ N._+ᴹ_ → M._*ᵣ_ MDefs.DistributesOverˡ _+_ ⟶ M._+ᴹ_
  *ᵣ-distribˡ {_+_ = _+_} *ᵣ-distribˡ x m n = injective $ begin
    ⟦ x M.*ᵣ (m + n) ⟧             ≈⟨ *ᵣ-homo (m + n) x ⟩
    ⟦ x ⟧ N.*ᵣ (m + n)             ≈⟨ *ᵣ-distribˡ ⟦ x ⟧ m n ⟩
    ⟦ x ⟧ N.*ᵣ m N.+ᴹ ⟦ x ⟧ N.*ᵣ n ≈˘⟨ +ᴹ-cong′ (*ᵣ-homo m x) (*ᵣ-homo n x) ⟩
    ⟦ x M.*ᵣ m ⟧ N.+ᴹ ⟦ x M.*ᵣ n ⟧ ≈˘⟨ +ᴹ-homo (x M.*ᵣ m) (x M.*ᵣ n) ⟩
    ⟦ x M.*ᵣ m M.+ᴹ x M.*ᵣ n ⟧     ∎

  *ᵣ-identityʳ : NDefs.RightIdentity 1# N._*ᵣ_ → MDefs.RightIdentity 1# M._*ᵣ_
  *ᵣ-identityʳ {1# = 1#} *ᵣ-identityʳ m = injective $ begin
    ⟦ m M.*ᵣ 1# ⟧ ≈⟨ *ᵣ-homo 1# m ⟩
    ⟦ m ⟧ N.*ᵣ 1# ≈⟨ *ᵣ-identityʳ ⟦ m ⟧ ⟩
    ⟦ m ⟧         ∎

  *ᵣ-assoc : NDefs.RightCongruent N._*ᵣ_ → NDefs.Associative _*_ N._*ᵣ_ → MDefs.Associative _*_ M._*ᵣ_
  *ᵣ-assoc {_*_ = _*_} *ᵣ-congʳ *ᵣ-assoc m x y = injective $ begin
    ⟦ m M.*ᵣ x M.*ᵣ y ⟧ ≈⟨ *ᵣ-homo y (m M.*ᵣ x) ⟩
    ⟦ m M.*ᵣ x ⟧ N.*ᵣ y ≈⟨ *ᵣ-congʳ (*ᵣ-homo x m) ⟩
    ⟦ m ⟧ N.*ᵣ x N.*ᵣ y ≈⟨ *ᵣ-assoc ⟦ m ⟧ x y ⟩
    ⟦ m ⟧ N.*ᵣ (x * y)  ≈˘⟨ *ᵣ-homo (x * y) m ⟩
    ⟦ m M.*ᵣ (x * y) ⟧  ∎

  *ᵣ-zeroˡ : NDefs.RightCongruent N._*ᵣ_ → NDefs.LeftZero N.0ᴹ N._*ᵣ_ → MDefs.LeftZero M.0ᴹ M._*ᵣ_
  *ᵣ-zeroˡ *ᵣ-congʳ *ᵣ-zeroˡ x = injective $ begin
    ⟦ M.0ᴹ M.*ᵣ x ⟧ ≈⟨ *ᵣ-homo x M.0ᴹ ⟩
    ⟦ M.0ᴹ ⟧ N.*ᵣ x ≈⟨ *ᵣ-congʳ 0ᴹ-homo ⟩
    N.0ᴹ N.*ᵣ x     ≈⟨ *ᵣ-zeroˡ x ⟩
    N.0ᴹ            ≈˘⟨ 0ᴹ-homo ⟩
    ⟦ M.0ᴹ ⟧        ∎

  *ᵣ-distribʳ : NDefs.RightCongruent N._*ᵣ_ → N._*ᵣ_ NDefs.DistributesOverʳ N._+ᴹ_ → M._*ᵣ_ MDefs.DistributesOverʳ M._+ᴹ_
  *ᵣ-distribʳ *ᵣ-congʳ *ᵣ-distribʳ x m n = injective $ begin
    ⟦ (m M.+ᴹ n) M.*ᵣ x ⟧          ≈⟨ *ᵣ-homo x (m M.+ᴹ n) ⟩
    ⟦ m M.+ᴹ n ⟧ N.*ᵣ x            ≈⟨ *ᵣ-congʳ (+ᴹ-homo m n) ⟩
    (⟦ m ⟧ N.+ᴹ ⟦ n ⟧) N.*ᵣ x      ≈⟨ *ᵣ-distribʳ x ⟦ m ⟧ ⟦ n ⟧ ⟩
    ⟦ m ⟧ N.*ᵣ x N.+ᴹ ⟦ n ⟧ N.*ᵣ x ≈˘⟨ +ᴹ-cong′ (*ᵣ-homo x m) (*ᵣ-homo x n) ⟩
    ⟦ m M.*ᵣ x ⟧ N.+ᴹ ⟦ n M.*ᵣ x ⟧ ≈˘⟨ +ᴹ-homo (m M.*ᵣ x) (n M.*ᵣ x) ⟩
    ⟦ m M.*ᵣ x M.+ᴹ n M.*ᵣ x ⟧     ∎

------------------------------------------------------------------------
-- Structures

module _ (R-isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#) where

  private
    R-semiring : Semiring _ _
    R-semiring = record { isSemiring = R-isSemiring }

  isRightSemimodule
    : IsRightSemimodule R-semiring N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N._*ᵣ_
    → IsRightSemimodule R-semiring M._≈ᴹ_ M._+ᴹ_ M.0ᴹ M._*ᵣ_
  isRightSemimodule isRightSemimodule = record
    { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid NN.+ᴹ-isCommutativeMonoid
    ; isPrerightSemimodule = record
      { *ᵣ-cong = *ᵣ-cong NN.+ᴹ-isMagma NN.*ᵣ-cong
      ; *ᵣ-zeroʳ = *ᵣ-zeroʳ NN.+ᴹ-isMagma NN.*ᵣ-zeroʳ
      ; *ᵣ-distribˡ = *ᵣ-distribˡ NN.+ᴹ-isMagma NN.*ᵣ-distribˡ
      ; *ᵣ-identityʳ = *ᵣ-identityʳ NN.+ᴹ-isMagma NN.*ᵣ-identityʳ
      ; *ᵣ-assoc = *ᵣ-assoc NN.+ᴹ-isMagma NN.*ᵣ-congʳ NN.*ᵣ-assoc
      ; *ᵣ-zeroˡ = *ᵣ-zeroˡ NN.+ᴹ-isMagma NN.*ᵣ-congʳ NN.*ᵣ-zeroˡ
      ; *ᵣ-distribʳ = *ᵣ-distribʳ NN.+ᴹ-isMagma NN.*ᵣ-congʳ NN.*ᵣ-distribʳ
      }
    } where module NN = IsRightSemimodule isRightSemimodule
