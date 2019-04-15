------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of pointwise equality for containers
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Container.Relation.Binary.Pointwise.Properties where

open import Axiom.Extensionality.Propositional
open import Data.Container.Core
open import Data.Container.Relation.Binary.Pointwise
open import Data.Product using (_,_; Σ-syntax; -,_)
open import Level using (_⊔_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; subst; cong)

module _ {s p x r} {X : Set x} (C : Container s p) (R : Rel X r) where

  refl : Reflexive R → Reflexive (Pointwise C R)
  refl R-refl = P.refl , λ p → R-refl

  sym : Symmetric R → Symmetric (Pointwise C R)
  sym R-sym (P.refl , f) = P.refl , λ p → R-sym (f p)

  trans : Transitive R → Transitive (Pointwise C R)
  trans R-trans (P.refl , f) (P.refl , g) = P.refl , λ p → R-trans (f p) (g p)

private

  -- Note that, if propositional equality were extensional, then
  -- Eq _≡_ and _≡_ would coincide.

  Eq⇒≡ : ∀ {s p x} {C : Container s p} {X : Set x} {xs ys : ⟦ C ⟧ X} →
         Extensionality p x → Pointwise C _≡_ xs ys → xs ≡ ys
  Eq⇒≡ ext (P.refl , f≈f′) = cong -,_ (ext f≈f′)
