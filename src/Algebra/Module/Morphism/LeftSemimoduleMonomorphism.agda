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
open RawLeftSemimodule M₁ renaming (Carrierᴹ to A; _≈ᴹ_ to _≈ᴹ₁_; _+ᴹ_ to _+ᴹ_; 0ᴹ to 0ᴹ₁; _*ₗ_ to _*ₗ_)
open RawLeftSemimodule M₂ renaming (Carrierᴹ to B; _≈ᴹ_ to _≈ᴹ₂_; _+ᴹ_ to _⊕ᴹ_; 0ᴹ to 0ᴹ₂; _*ₗ_ to _⊛ₗ_)

open import Algebra.Core
open import Algebra.Module.Definitions.Left R _≈ᴹ₁_
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

module _
  {_≈_ : Rel R ℓr} {_+_ _*_ : Op₂ R} {0# 1# : R}
  (R-isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#)
  (let R-semiring = record { isSemiring = R-isSemiring })
  (⊕-isLeftSemimodule : IsLeftSemimodule R-semiring _≈ᴹ₂_ _⊕ᴹ_ 0ᴹ₂ _⊛ₗ_)
  where

  open IsLeftSemimodule ⊕-isLeftSemimodule
    renaming (*ₗ-cong to ⊛ₗ-cong; *ₗ-congˡ to ⊛ₗ-congˡ; *ₗ-zeroˡ to ⊛ₗ-zeroˡ; *ₗ-distribʳ to ⊛ₗ-distribʳ; *ₗ-identityˡ to ⊛ₗ-identityˡ; *ₗ-assoc to ⊛ₗ-assoc; *ₗ-zeroʳ to ⊛ₗ-zeroʳ; *ₗ-distribˡ to ⊛ₗ-distribˡ; +ᴹ-cong to ⊕ᴹ-cong)
  open SetoidReasoning ≈ᴹ-setoid

  *ₗ-cong : Congruent _≈_ _*ₗ_
  *ₗ-cong {x} {y} {u} {v} x≈y u≈ᴹv = injective $ begin
    ⟦ x *ₗ u ⟧ ≈⟨ *ₗ-homo x u ⟩
    x ⊛ₗ ⟦ u ⟧ ≈⟨ ⊛ₗ-cong x≈y (⟦⟧-cong u≈ᴹv) ⟩
    y ⊛ₗ ⟦ v ⟧ ≈˘⟨ *ₗ-homo y v ⟩
    ⟦ y *ₗ v ⟧ ∎

  *ₗ-zeroˡ : LeftZero 0# 0ᴹ₁ _*ₗ_
  *ₗ-zeroˡ x = injective $ begin
    ⟦ 0# *ₗ x ⟧ ≈⟨ *ₗ-homo 0# x ⟩
    0# ⊛ₗ ⟦ x ⟧ ≈⟨ ⊛ₗ-zeroˡ ⟦ x ⟧ ⟩
    0ᴹ₂         ≈˘⟨ 0ᴹ-homo ⟩
    ⟦ 0ᴹ₁ ⟧     ∎

  *ₗ-distribʳ : _*ₗ_ DistributesOverʳ _+_ ⟶ _+ᴹ_
  *ₗ-distribʳ x m n = injective $ begin
    ⟦ (m + n) *ₗ x ⟧         ≈⟨ *ₗ-homo (m + n) x ⟩
    (m + n) ⊛ₗ ⟦ x ⟧         ≈⟨ ⊛ₗ-distribʳ ⟦ x ⟧ m n ⟩
    m ⊛ₗ ⟦ x ⟧ ⊕ᴹ n ⊛ₗ ⟦ x ⟧ ≈˘⟨ ⊕ᴹ-cong (*ₗ-homo m x) (*ₗ-homo n x) ⟩
    ⟦ m *ₗ x ⟧ ⊕ᴹ ⟦ n *ₗ x ⟧ ≈˘⟨ +ᴹ-homo (m *ₗ x) (n *ₗ x) ⟩
    ⟦ m *ₗ x +ᴹ n *ₗ x ⟧     ∎

  *ₗ-identityˡ : LeftIdentity 1# _*ₗ_
  *ₗ-identityˡ m = injective $ begin
    ⟦ 1# *ₗ m ⟧ ≈⟨ *ₗ-homo 1# m ⟩
    1# ⊛ₗ ⟦ m ⟧ ≈⟨ ⊛ₗ-identityˡ ⟦ m ⟧ ⟩
    ⟦ m ⟧       ∎

  *ₗ-assoc : Associative _*_ _*ₗ_
  *ₗ-assoc x y m = injective $ begin
    ⟦ (x * y) *ₗ m ⟧ ≈⟨ *ₗ-homo (x * y) m ⟩
    (x * y) ⊛ₗ ⟦ m ⟧ ≈⟨ ⊛ₗ-assoc x y ⟦ m ⟧ ⟩
    x ⊛ₗ y ⊛ₗ ⟦ m ⟧  ≈˘⟨ ⊛ₗ-congˡ (*ₗ-homo y m) ⟩
    x ⊛ₗ ⟦ y *ₗ m ⟧  ≈˘⟨ *ₗ-homo x (y *ₗ m) ⟩
    ⟦ x *ₗ y *ₗ m ⟧  ∎

  *ₗ-zeroʳ : RightZero 0ᴹ₁ _*ₗ_
  *ₗ-zeroʳ x = injective $ begin
    ⟦ x *ₗ 0ᴹ₁ ⟧ ≈⟨ *ₗ-homo x 0ᴹ₁ ⟩
    x ⊛ₗ ⟦ 0ᴹ₁ ⟧ ≈⟨ ⊛ₗ-congˡ 0ᴹ-homo ⟩
    x ⊛ₗ 0ᴹ₂     ≈⟨ ⊛ₗ-zeroʳ x ⟩
    0ᴹ₂          ≈˘⟨ 0ᴹ-homo ⟩
    ⟦ 0ᴹ₁ ⟧      ∎

  *ₗ-distribˡ : _*ₗ_ DistributesOverˡ _+ᴹ_
  *ₗ-distribˡ x m n = injective $ begin
    ⟦ x *ₗ (m +ᴹ n) ⟧        ≈⟨ *ₗ-homo x (m +ᴹ n) ⟩
    x ⊛ₗ ⟦ m +ᴹ n ⟧          ≈⟨ ⊛ₗ-congˡ (+ᴹ-homo m n) ⟩
    x ⊛ₗ (⟦ m ⟧ ⊕ᴹ ⟦ n ⟧)    ≈⟨ ⊛ₗ-distribˡ x ⟦ m ⟧ ⟦ n ⟧ ⟩
    x ⊛ₗ ⟦ m ⟧ ⊕ᴹ x ⊛ₗ ⟦ n ⟧ ≈˘⟨ ⊕ᴹ-cong (*ₗ-homo x m) (*ₗ-homo x n) ⟩
    ⟦ x *ₗ m ⟧ ⊕ᴹ ⟦ x *ₗ n ⟧ ≈˘⟨ +ᴹ-homo (x *ₗ m) (x *ₗ n) ⟩
    ⟦ x *ₗ m +ᴹ x *ₗ n ⟧     ∎
    
------------------------------------------------------------------------
-- Structures

isLeftSemimodule :
  {_≈_ : Rel R ℓr} {_+_ _*_ : Op₂ R} {0# 1# : R}
  (R-isSemiring : IsSemiring _≈_ _+_ _*_ 0# 1#)
  (let R-semiring = record { isSemiring = R-isSemiring })
  → IsLeftSemimodule R-semiring _≈ᴹ₂_ _⊕ᴹ_ 0ᴹ₂ _⊛ₗ_
  → IsLeftSemimodule R-semiring _≈ᴹ₁_ _+ᴹ_ 0ᴹ₁ _*ₗ_
isLeftSemimodule isSemiring isLeftSemimodule = record
  { +ᴹ-isCommutativeMonoid = +ᴹ-isCommutativeMonoid M.+ᴹ-isCommutativeMonoid
  ; isPreleftSemimodule = record
    { *ₗ-cong = *ₗ-cong isSemiring isLeftSemimodule
    ; *ₗ-zeroˡ = *ₗ-zeroˡ isSemiring isLeftSemimodule
    ; *ₗ-distribʳ = *ₗ-distribʳ isSemiring isLeftSemimodule
    ; *ₗ-identityˡ = *ₗ-identityˡ isSemiring isLeftSemimodule
    ; *ₗ-assoc = *ₗ-assoc isSemiring isLeftSemimodule
    ; *ₗ-zeroʳ = *ₗ-zeroʳ isSemiring isLeftSemimodule
    ; *ₗ-distribˡ = *ₗ-distribˡ isSemiring isLeftSemimodule
    }
  } where module M = IsLeftSemimodule isLeftSemimodule
