------------------------------------------------------------------------
-- The Agda standard library
--
-- Consequences of a morphism between monoids
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Algebra.Morphism
open RawMonoid using (Carrier; _≈_)

module Algebra.Morphism.RawMonoid
  {a b ℓ₁ ℓ₂} {From : RawMonoid b ℓ₂} {To : RawMonoid a ℓ₁}
  {to : Carrier From → Carrier To}
  (isRawMonoidMorphism : IsRawMonoidMorphism From To to)
  (to-injective : ∀ {x y} → _≈_ To (to x) (to y) → _≈_ From x y)
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

open IsRawMonoidMorphism isRawMonoidMorphism
open SetoidReasoning T-setoid

------------------------------------------------------------------------
-- Export all properties of magma morphisms

open import Algebra.Morphism.RawMagma magma-homo to-injective public

------------------------------------------------------------------------
-- Properties

identityˡ-homo : LeftIdentity T._≈_ T.ε _⊕_ → LeftIdentity F._≈_ F.ε _∙_
identityˡ-homo idˡ x = to-injective (begin
  to (F.ε ∙ x)  ≈⟨ ∙-homo F.ε x ⟩
  to F.ε ⊕ to x ≈⟨ T-∙-congʳ ε-homo ⟩
  T.ε ⊕ to x    ≈⟨ idˡ (to x) ⟩
  to x          ∎)

identityʳ-homo : RightIdentity T._≈_ T.ε _⊕_ → RightIdentity F._≈_ F.ε _∙_
identityʳ-homo idʳ x = to-injective (begin
  to (x ∙ F.ε)  ≈⟨ ∙-homo x F.ε ⟩
  to x ⊕ to F.ε ≈⟨ T-∙-congˡ ε-homo ⟩
  to x ⊕ T.ε    ≈⟨ idʳ (to x) ⟩
  to x          ∎)

identity-homo : Identity T._≈_ T.ε _⊕_ → Identity F._≈_ F.ε _∙_
identity-homo (idˡ , idʳ) = identityˡ-homo idˡ , identityʳ-homo idʳ
