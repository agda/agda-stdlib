------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of pointwise equality for indexed containers
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Container.Indexed.Relation.Binary.Pointwise.Properties where

open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.Container.Indexed.Core using (Container; ⟦_⟧)
open import Data.Container.Indexed.Relation.Binary.Pointwise
  using (Pointwise)
open import Data.Product.Base using (_,_; Σ-syntax; -,_)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; subst; cong)

private variable
  ℓᵉ ℓᵖ ℓˢ ℓˣ : Level
  I O : Set _

module _
  (C : Container I O ℓˢ ℓᵖ) {X : I → Set ℓˣ}
  (R : (i : I) → Rel (X i) ℓᵉ)
  {o : O}
  where

  refl : (∀ i → Reflexive (R i)) → Reflexive (Pointwise C R o)
  refl R-refl = ≡.refl , λ p → R-refl _

  sym : (∀ i → Symmetric (R i)) → Symmetric (Pointwise C R o)
  sym R-sym (≡.refl , f) = ≡.refl , λ p → R-sym _ (f p)

  trans : (∀ i → Transitive (R i)) → Transitive (Pointwise C R o)
  trans R-trans (≡.refl , f) (≡.refl , g) = ≡.refl , λ p → R-trans _ (f p) (g p)

-- If propositional equality is extensional, then `Eq _≡_` and `_≡_` coincide.
Eq⇒≡ : {C : Container I O ℓˢ ℓᵖ} {X : I → Set ℓˣ} {R : (i : I) → Rel (X i) ℓᵉ}
       {o : O} {xs ys : ⟦ C ⟧ X o} →
       Extensionality ℓᵖ ℓˣ →
       Pointwise C (λ (i : I) → _≡_ {A = X i}) o xs ys →
       xs ≡ ys
Eq⇒≡ ext (≡.refl , f≈f′) = cong -,_ (ext f≈f′)
