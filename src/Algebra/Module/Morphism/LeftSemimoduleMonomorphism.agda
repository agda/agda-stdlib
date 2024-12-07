------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between left semimodules
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Module.Bundles.Raw
open import Algebra.Module.Morphism.Structures

module Algebra.Module.Morphism.LeftSemimoduleMonomorphism
  {r a b ℓ₁ ℓ₂} {R : Set r} {M₁ : RawLeftSemimodule R a ℓ₁} {M₂ : RawLeftSemimodule R b ℓ₂} {⟦_⟧}
  (isLeftSemimoduleMonomorphism : IsLeftSemimoduleMonomorphism M₁ M₂ ⟦_⟧)
  where

open IsLeftSemimoduleMonomorphism isLeftSemimoduleMonomorphism
private
  module M = RawLeftSemimodule M₁
  module N = RawLeftSemimodule M₂

open import Algebra.Bundles
open import Algebra.Core
import Algebra.Module.Definitions.Left as LeftDefs
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
-- Re-export most properties of monoid monomorphisms

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

----------------------------------------------------------------------------------
-- Properties

module _ (+ᴹ-isMagma : IsMagma N._≈ᴹ_ N._+ᴹ_) where

  open IsMagma +ᴹ-isMagma
    using (setoid)
    renaming (∙-cong to +ᴹ-cong′)
  open SetoidReasoning setoid

  module MDefs = LeftDefs R M._≈ᴹ_
  module NDefs = LeftDefs R N._≈ᴹ_

  *ₗ-cong : NDefs.Congruent _≈_ N._*ₗ_ → MDefs.Congruent _≈_ M._*ₗ_
  *ₗ-cong *ₗ-cong {x} {y} {u} {v} x≈y u≈ᴹv = injective $ begin
    ⟦ x M.*ₗ u ⟧ ≈⟨ *ₗ-homo x u ⟩
    x N.*ₗ ⟦ u ⟧ ≈⟨ *ₗ-cong x≈y (⟦⟧-cong u≈ᴹv) ⟩
    y N.*ₗ ⟦ v ⟧ ≈˘⟨ *ₗ-homo y v ⟩
    ⟦ y M.*ₗ v ⟧ ∎

  *ₗ-zeroˡ : NDefs.LeftZero 0# N.0ᴹ N._*ₗ_ → MDefs.LeftZero 0# M.0ᴹ M._*ₗ_
  *ₗ-zeroˡ {0# = 0#} *ₗ-zeroˡ x = injective $ begin
    ⟦ 0# M.*ₗ x ⟧ ≈⟨ *ₗ-homo 0# x ⟩
    0# N.*ₗ ⟦ x ⟧ ≈⟨ *ₗ-zeroˡ ⟦ x ⟧ ⟩
    N.0ᴹ          ≈˘⟨ 0ᴹ-homo ⟩
    ⟦ M.0ᴹ ⟧      ∎

  *ₗ-distribʳ : N._*ₗ_ NDefs.DistributesOverʳ _+_ ⟶ N._+ᴹ_ → M._*ₗ_ MDefs.DistributesOverʳ _+_ ⟶ M._+ᴹ_
  *ₗ-distribʳ {_+_ = _+_} *ₗ-distribʳ x m n = injective $ begin
    ⟦ (m + n) M.*ₗ x ⟧             ≈⟨ *ₗ-homo (m + n) x ⟩
    (m + n) N.*ₗ ⟦ x ⟧             ≈⟨ *ₗ-distribʳ ⟦ x ⟧ m n ⟩
    m N.*ₗ ⟦ x ⟧ N.+ᴹ n N.*ₗ ⟦ x ⟧ ≈˘⟨ +ᴹ-cong′ (*ₗ-homo m x) (*ₗ-homo n x) ⟩
    ⟦ m M.*ₗ x ⟧ N.+ᴹ ⟦ n M.*ₗ x ⟧ ≈˘⟨ +ᴹ-homo (m M.*ₗ x) (n M.*ₗ x) ⟩
    ⟦ m M.*ₗ x M.+ᴹ n M.*ₗ x ⟧     ∎

  *ₗ-identityˡ : NDefs.LeftIdentity 1# N._*ₗ_ → MDefs.LeftIdentity 1# M._*ₗ_
  *ₗ-identityˡ {1# = 1#} *ₗ-identityˡ m = injective $ begin
    ⟦ 1# M.*ₗ m ⟧ ≈⟨ *ₗ-homo 1# m ⟩
    1# N.*ₗ ⟦ m ⟧ ≈⟨ *ₗ-identityˡ ⟦ m ⟧ ⟩
    ⟦ m ⟧         ∎

  *ₗ-assoc : NDefs.LeftCongruent N._*ₗ_ → NDefs.Associative _*_ N._*ₗ_ → MDefs.Associative _*_ M._*ₗ_
  *ₗ-assoc {_*_ = _*_} *ₗ-congˡ *ₗ-assoc x y m = injective $ begin
    ⟦ (x * y) M.*ₗ m ⟧  ≈⟨ *ₗ-homo (x * y) m ⟩
    (x * y) N.*ₗ ⟦ m ⟧  ≈⟨ *ₗ-assoc x y ⟦ m ⟧ ⟩
    x N.*ₗ y N.*ₗ ⟦ m ⟧ ≈˘⟨ *ₗ-congˡ (*ₗ-homo y m) ⟩
    x N.*ₗ ⟦ y M.*ₗ m ⟧ ≈˘⟨ *ₗ-homo x (y M.*ₗ m) ⟩
    ⟦ x M.*ₗ y M.*ₗ m ⟧ ∎

  *ₗ-zeroʳ : NDefs.LeftCongruent N._*ₗ_ → NDefs.RightZero N.0ᴹ N._*ₗ_ → MDefs.RightZero M.0ᴹ M._*ₗ_
  *ₗ-zeroʳ *ₗ-congˡ *ₗ-zeroʳ x = injective $ begin
    ⟦ x M.*ₗ M.0ᴹ ⟧ ≈⟨ *ₗ-homo x M.0ᴹ ⟩
    x N.*ₗ ⟦ M.0ᴹ ⟧ ≈⟨ *ₗ-congˡ 0ᴹ-homo ⟩
    x N.*ₗ N.0ᴹ     ≈⟨ *ₗ-zeroʳ x ⟩
    N.0ᴹ            ≈˘⟨ 0ᴹ-homo ⟩
    ⟦ M.0ᴹ ⟧        ∎

  *ₗ-distribˡ : NDefs.LeftCongruent N._*ₗ_ → N._*ₗ_ NDefs.DistributesOverˡ N._+ᴹ_ → M._*ₗ_ MDefs.DistributesOverˡ M._+ᴹ_
  *ₗ-distribˡ *ₗ-congˡ *ₗ-distribˡ x m n = injective $ begin
    ⟦ x M.*ₗ (m M.+ᴹ n) ⟧          ≈⟨ *ₗ-homo x (m M.+ᴹ n) ⟩
    x N.*ₗ ⟦ m M.+ᴹ n ⟧            ≈⟨ *ₗ-congˡ (+ᴹ-homo m n) ⟩
    x N.*ₗ (⟦ m ⟧ N.+ᴹ ⟦ n ⟧)      ≈⟨ *ₗ-distribˡ x ⟦ m ⟧ ⟦ n ⟧ ⟩
    x N.*ₗ ⟦ m ⟧ N.+ᴹ x N.*ₗ ⟦ n ⟧ ≈˘⟨ +ᴹ-cong′ (*ₗ-homo x m) (*ₗ-homo x n) ⟩
    ⟦ x M.*ₗ m ⟧ N.+ᴹ ⟦ x M.*ₗ n ⟧ ≈˘⟨ +ᴹ-homo (x M.*ₗ m) (x M.*ₗ n) ⟩
    ⟦ x M.*ₗ m M.+ᴹ x M.*ₗ n ⟧     ∎

------------------------------------------------------------------------
-- Structures

module _ (R-isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#) where

  private
    R-semiring : Semiring _ _
    R-semiring = record { isSemiring = R-isSemiring }

  isLeftSemimodule
    : IsLeftSemimodule R-semiring N._≈ᴹ_ N._+ᴹ_ N.0ᴹ N._*ₗ_
    → IsLeftSemimodule R-semiring M._≈ᴹ_ M._+ᴹ_ M.0ᴹ M._*ₗ_
  isLeftSemimodule isLeftSemimodule = record
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
    } where module NN = IsLeftSemimodule isLeftSemimodule
