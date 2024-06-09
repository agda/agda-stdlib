------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of pointwise equality for containers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Relation.Binary.Pointwise.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Container.Core using (Container; ⟦_⟧)
open import Data.Container.Relation.Binary.Pointwise
  using (Pointwise; _,_)
open import Data.Product.Base using (_,_; Σ-syntax; -,_)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
  using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; subst; cong)

module _ {s p x r} {X : Set x} (C : Container s p) (R : Rel X r) where

  refl : Reflexive R → Reflexive (Pointwise C R)
  refl R-refl = ≡.refl , λ p → R-refl

  sym : Symmetric R → Symmetric (Pointwise C R)
  sym R-sym (≡.refl , f) = ≡.refl , λ p → R-sym (f p)

  trans : Transitive R → Transitive (Pointwise C R)
  trans R-trans (≡.refl , f) (≡.refl , g) = ≡.refl , λ p → R-trans (f p) (g p)

private

  -- Note that, if propositional equality were extensional, then
  -- Eq _≡_ and _≡_ would coincide.

  Eq⇒≡ : ∀ {s p x} {C : Container s p} {X : Set x} {xs ys : ⟦ C ⟧ X} →
         Extensionality p x → Pointwise C _≡_ xs ys → xs ≡ ys
  Eq⇒≡ ext (≡.refl , f≈f′) = cong -,_ (ext f≈f′)
