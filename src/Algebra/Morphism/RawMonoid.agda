------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a morphism between monoids
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Morphism
open import Function
open RawMonoid using (Carrier; _≈_)

module Algebra.Morphism.RawMonoid
  {a b ℓ₁ ℓ₂} {From : RawMonoid b ℓ₂} {To : RawMonoid a ℓ₁}
  {f : Carrier From → Carrier To}
  (f-isRawMonoidMorphism : IsRawMonoidMorphism From To f)
  (f-injective : Injective (_≈_ From) (_≈_ To) f)
  where

open import Relation.Binary
open import Algebra
open import Algebra.Structures
open import Algebra.FunctionProperties
open import Data.Product using (_,_)
open import Function
open import Level
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

private
  module F = RawMonoid From
  module T = RawMonoid To

open Definitions F.Carrier T.Carrier T._≈_
open T using () renaming (_∙_ to _⊕_)
open F using (_∙_)

open IsRawMonoidMorphism f-isRawMonoidMorphism
open SetoidReasoning T-setoid

------------------------------------------------------------------------
-- Export all properties of magma morphisms

open import Algebra.Morphism.RawMagma magma-homo f-injective public

------------------------------------------------------------------------
-- Properties

identityˡ-homo : LeftIdentity T._≈_ T.ε _⊕_ → LeftIdentity F._≈_ F.ε _∙_
identityˡ-homo idˡ x = f-injective (begin
  f (F.ε ∙ x)  ≈⟨ ∙-homo F.ε x ⟩
  f F.ε ⊕ f x ≈⟨ T-∙-congʳ ε-homo ⟩
  T.ε ⊕ f x    ≈⟨ idˡ (f x) ⟩
  f x          ∎)

identityʳ-homo : RightIdentity T._≈_ T.ε _⊕_ → RightIdentity F._≈_ F.ε _∙_
identityʳ-homo idʳ x = f-injective (begin
  f (x ∙ F.ε)  ≈⟨ ∙-homo x F.ε ⟩
  f x ⊕ f F.ε ≈⟨ T-∙-congˡ ε-homo ⟩
  f x ⊕ T.ε    ≈⟨ idʳ (f x) ⟩
  f x          ∎)

identity-homo : Identity T._≈_ T.ε _⊕_ → Identity F._≈_ F.ε _∙_
identity-homo (idˡ , idʳ) = identityˡ-homo idˡ , identityʳ-homo idʳ

------------------------------------------------------------------------
-- Properties

isMonoid-homo : IsMonoid T._≈_ _⊕_ T.ε → IsMonoid F._≈_ _∙_ F.ε
isMonoid-homo isMonoid = record
  { isSemigroup = isSemigroup-homo isSemigroup
  ; identity    = identity-homo identity
  } where open IsMonoid isMonoid

isCommutativeMonoid-homo : IsCommutativeMonoid T._≈_ _⊕_ T.ε →
                           IsCommutativeMonoid F._≈_ _∙_ F.ε
isCommutativeMonoid-homo isCommMonoid = record
  { isSemigroup = isSemigroup-homo isSemigroup
  ; identityˡ   = identityˡ-homo identityˡ
  ; comm        = comm-homo comm
  } where open IsCommutativeMonoid isCommMonoid
