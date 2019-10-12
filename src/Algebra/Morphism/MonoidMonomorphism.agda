------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a monomorphism between monoid-like structures
------------------------------------------------------------------------

-- See Data.Nat.Binary.Properties for examples of how this and similar
-- modules can be used to easily translate properties between types.

{-# OPTIONS --without-K --safe #-}

open import Algebra.Core
open import Algebra.Structures
open import Algebra.Morphism.Structures
open import Relation.Binary.Core

module Algebra.Morphism.MonoidMonomorphism
  {a b} {A : Set a} {B : Set b}
  {ℓ₁ ℓ₂} {_≈₁_ : Rel A ℓ₁} {_≈₂_ : Rel B ℓ₂}
  {_∙_ : Op₂ A} {_◦_ : Op₂ B} {f : A → B}
  {ε₁ : A} {ε₂ : B}
  (isMonoidMonomorphism : IsMonoidMonomorphism _≈₁_ _≈₂_ _∙_ _◦_ ε₁ ε₂ f)
  (◦-isMagma : IsMagma _≈₂_ _◦_)
  where

open IsMonoidMonomorphism isMonoidMonomorphism
open IsMagma ◦-isMagma renaming (∙-cong to ◦-cong)

open import Relation.Binary
open import Algebra.Definitions
open import Data.Product using (map)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

open SetoidReasoning setoid

------------------------------------------------------------------------
-- Re-export all properties of magma monomorphisms

open import Algebra.Morphism.MagmaMonomorphism
  isMagmaMonomorphism ◦-isMagma public

------------------------------------------------------------------------
-- Properties

identityˡ : LeftIdentity _≈₂_ ε₂ _◦_ → LeftIdentity _≈₁_ ε₁ _∙_
identityˡ idˡ x = injective (begin
  f (ε₁ ∙ x)  ≈⟨ homo ε₁ x ⟩
  f ε₁ ◦ f x  ≈⟨ ◦-cong ε-homo refl ⟩
  ε₂ ◦ f x    ≈⟨ idˡ (f x) ⟩
  f x         ∎)

identityʳ : RightIdentity _≈₂_ ε₂ _◦_ → RightIdentity _≈₁_ ε₁ _∙_
identityʳ idʳ x = injective (begin
  f (x ∙ ε₁)  ≈⟨ homo x ε₁ ⟩
  f x ◦ f ε₁  ≈⟨ ◦-cong refl ε-homo ⟩
  f x ◦ ε₂    ≈⟨ idʳ (f x) ⟩
  f x         ∎)

identity : Identity _≈₂_ ε₂ _◦_ → Identity _≈₁_ ε₁ _∙_
identity = map identityˡ identityʳ

zeroˡ : LeftZero _≈₂_ ε₂ _◦_ → LeftZero _≈₁_ ε₁ _∙_
zeroˡ zeˡ x = injective (begin
  f (ε₁ ∙ x) ≈⟨  homo ε₁ x ⟩
  f ε₁ ◦ f x ≈⟨  ◦-cong ε-homo refl ⟩
  ε₂   ◦ f x ≈⟨  zeˡ (f x) ⟩
  ε₂         ≈˘⟨ ε-homo ⟩
  f ε₁       ∎)

zeroʳ : RightZero _≈₂_ ε₂ _◦_ → RightZero _≈₁_ ε₁ _∙_
zeroʳ zeʳ x = injective (begin
  f (x ∙ ε₁) ≈⟨  homo x ε₁ ⟩
  f x ◦ f ε₁ ≈⟨  ◦-cong refl ε-homo ⟩
  f x ◦ ε₂   ≈⟨  zeʳ (f x) ⟩
  ε₂         ≈˘⟨ ε-homo ⟩
  f ε₁       ∎)

zero : Zero _≈₂_ ε₂ _◦_ → Zero _≈₁_ ε₁ _∙_
zero = map zeroˡ zeroʳ

------------------------------------------------------------------------
-- Properties

isMonoid : IsMonoid _≈₂_ _◦_ ε₂ → IsMonoid _≈₁_ _∙_ ε₁
isMonoid isMonoid = record
  { isSemigroup = isSemigroup M.isSemigroup
  ; identity    = identity    M.identity
  } where module M = IsMonoid isMonoid

isCommutativeMonoid : IsCommutativeMonoid _≈₂_ _◦_ ε₂ →
                      IsCommutativeMonoid _≈₁_ _∙_ ε₁
isCommutativeMonoid isCommMonoid = record
  { isSemigroup = isSemigroup C.isSemigroup
  ; identityˡ   = identityˡ   C.identityˡ
  ; comm        = comm        C.comm
  } where module C = IsCommutativeMonoid isCommMonoid
