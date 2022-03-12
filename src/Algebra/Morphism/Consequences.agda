------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of Magma homomorphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Morphism.Consequences where

open import Algebra using (Magma)
open import Algebra.Morphism.Definitions
open import Data.Product using (_,_)
open import Function.Base using (id; _∘_)
open import Function.Definitions
import Relation.Binary.Reasoning.Setoid as EqR

---------------------------------------------------------------------------------
-- If f and g are mutually inverse maps between A and B, g is congruent,
-- f is a homomorphism, then g is a homomorphism.

module _ {α α= β β=} (M₁ : Magma α α=) (M₂ : Magma β β=) where

  private
    open module M₁ = Magma M₁ using () renaming (_≈_ to _≈₁_; _∙_ to _∙₁_)
    open module M₂ = Magma M₂ using () renaming (_≈_ to _≈₂_; _∙_ to _∙₂_)

  homomorphic₂-inv  : ∀ {f g} → Congruent _≈₂_ _≈₁_ g →
                      Inverseᵇ _≈₁_ _≈₂_ f g →
                      Homomorphic₂ _ _ _≈₂_ f _∙₁_ _∙₂_  →
                      Homomorphic₂ _ _ _≈₁_ g _∙₂_ _∙₁_
  homomorphic₂-inv {f} {g} g-cong (f∘g=id , g∘f=id) homo x y = begin
    g (x ∙₂ y)             ≈⟨ M₁.sym (g-cong (M₂.∙-cong (f∘g=id x) (f∘g=id y))) ⟩
    g (f (g x) ∙₂ f (g y)) ≈⟨ M₁.sym (g-cong (homo (g x) (g y))) ⟩
    g (f (g x ∙₁ g y))     ≈⟨ g∘f=id (g x ∙₁ g y) ⟩
    g x ∙₁ g y             ∎
    where open EqR M₁.setoid

  homomorphic₂-inj  : ∀ {f g} → Injective _≈₁_ _≈₂_ f →
                      Inverseˡ _≈₁_ _≈₂_ f g →
                      Homomorphic₂ _ _ _≈₂_ f _∙₁_ _∙₂_  →
                      Homomorphic₂ _ _ _≈₁_ g _∙₂_ _∙₁_
  homomorphic₂-inj {f} {g} inj invˡ homo x y = inj (begin
    f (g (x ∙₂ y))      ≈⟨ invˡ (x ∙₂ y) ⟩
    x ∙₂ y              ≈⟨ M₂.sym (M₂.∙-cong (invˡ x) (invˡ y)) ⟩
    f (g x) ∙₂ f (g y)  ≈⟨ M₂.sym (homo (g x) (g y)) ⟩
    f (g x ∙₁ g y)      ∎)
    where open EqR M₂.setoid
