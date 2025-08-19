------------------------------------------------------------------------
-- The Agda standard library
--
-- Order morphisms
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)

module Relation.Binary.Predomain.Morphism.Structures
  {a b} {A : Set a} {B : Set b}
  where

open import Data.Product.Base using (_,_)
open import Function.Base using (_∘_)
open import Function.Definitions using (Injective; Surjective; Bijective)
open import Level using (Level; suc; _⊔_)

open import Relation.Binary.Morphism.Definitions A B
open import Relation.Binary.Morphism.Structures
open import Relation.Binary.Predomain.Definitions
open import Relation.Binary.Predomain.Structures

private
  variable
    i ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    I : Set i
    x y : A
    f : I → A


------------------------------------------------------------------------
-- Scott continuous maps
------------------------------------------------------------------------

record IsContinuousHomomorphism i (_≈₁_ : Rel A ℓ₁) (_≈₂_ : Rel B ℓ₂)
                                (_≲₁_ : Rel A ℓ₃) (_≲₂_ : Rel B ℓ₄)
                                (⟦_⟧ : A → B) : Set (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄ ⊔ suc i)
                                where
  field
    isOrderHomomorphism : IsOrderHomomorphism _≈₁_ _≈₂_ _≲₁_ _≲₂_ ⟦_⟧
    ⋁-homo : MinimalUpperBoundAbove _≲₁_ {i = i} {I = I} f x y →
              MinimalUpperBoundAbove _≲₂_ (⟦_⟧ ∘ f) ⟦ x ⟧ ⟦ y ⟧


