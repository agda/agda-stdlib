------------------------------------------------------------------------
-- The Agda standard library
--
-- Pointwise lifting of binary relations to sigma types
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.Relation.Binary.Pointwise.Dependent where

open import Data.Product as Prod
open import Level
open import Function
open import Relation.Binary as B
  using (_⇒_; Setoid; IsEquivalence)
open import Relation.Binary.Indexed.Heterogeneous as I
  using (IREL; IRel; IndexedSetoid; IsIndexedEquivalence)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

------------------------------------------------------------------------
-- Pointwise lifting

infixr 4 _,_

record POINTWISE {a₁ a₂ b₁ b₂ ℓ₁ ℓ₂}
                 {A₁ : Set a₁} (B₁ : A₁ → Set b₁)
                 {A₂ : Set a₂} (B₂ : A₂ → Set b₂)
                 (_R₁_ : B.REL A₁ A₂ ℓ₁) (_R₂_ : IREL B₁ B₂ ℓ₂)
                 (xy₁ : Σ A₁ B₁) (xy₂ : Σ A₂ B₂)
                 : Set (a₁ ⊔ a₂ ⊔ b₁ ⊔ b₂ ⊔ ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    proj₁ : (proj₁ xy₁) R₁ (proj₁ xy₂)
    proj₂ : (proj₂ xy₁) R₂ (proj₂ xy₂)

open POINTWISE public

Pointwise : ∀ {a b ℓ₁ ℓ₂} {A : Set a} (B : A → Set b)
            (_R₁_ : B.Rel A ℓ₁) (_R₂_ : IRel B ℓ₂) → B.Rel (Σ A B) _
Pointwise B = POINTWISE B B

------------------------------------------------------------------------
-- Pointwise preserves many relational properties

module _ {a b ℓ₁ ℓ₂} {A : Set a} {B : A → Set b}
         {R : B.Rel A ℓ₁} {S : IRel B ℓ₂} where

  private
    R×S = Pointwise B R S

  refl : B.Reflexive R → I.Reflexive B S → B.Reflexive R×S
  refl refl₁ refl₂ = (refl₁ , refl₂)

  symmetric : B.Symmetric R → I.Symmetric B S → B.Symmetric R×S
  symmetric sym₁ sym₂ (x₁Rx₂ , y₁Ry₂) = (sym₁ x₁Rx₂ , sym₂ y₁Ry₂)

  transitive : B.Transitive R → I.Transitive B S → B.Transitive R×S
  transitive trans₁ trans₂ (x₁Rx₂ , y₁Ry₂) (x₂Rx₃ , y₂Ry₃) =
    (trans₁ x₁Rx₂ x₂Rx₃ , trans₂ y₁Ry₂ y₂Ry₃)

  isEquivalence : IsEquivalence R → IsIndexedEquivalence B S →
                  IsEquivalence R×S
  isEquivalence eq₁ eq₂ = record
    { refl  = refl       Eq.refl  IEq.refl
    ; sym   = symmetric  Eq.sym   IEq.sym
    ; trans = transitive Eq.trans IEq.trans
    } where
    module Eq = IsEquivalence eq₁
    module IEq = IsIndexedEquivalence eq₂

module _ {a b ℓ₁ ℓ₂} where

  setoid : (A : Setoid a ℓ₁) →
           IndexedSetoid (Setoid.Carrier A) b ℓ₂ →
           Setoid _ _
  setoid s₁ s₂ = record
    { isEquivalence = isEquivalence Eq.isEquivalence IEq.isEquivalence
    } where
    module Eq = Setoid s₁
    module IEq = IndexedSetoid s₂

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 0.15

Rel = Pointwise
{-# WARNING_ON_USAGE Rel
"Warning: Rel was deprecated in v0.15.
Please use Pointwise instead."
#-}

-- Version 0.15

REL = POINTWISE
{-# WARNING_ON_USAGE REL
"Warning: REL was deprecated in v1.0.
Please use POINTWISE instead."
#-}
