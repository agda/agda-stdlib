------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of Magma homomorphisms
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Algebra.Morphism.Consequences where

open import Algebra using (Magma)
open import Algebra.Morphism.Definitions using (Homomorphic₂)
open import Data.Product.Base using (_,_)
open import Function.Base using (id; _∘_; _$_)
open import Function.Consequences
  using (inverseʳ⇒injective)
open import Function.Definitions
  using (Injective; Congruent; Inverseᵇ; Inverseˡ)
import Relation.Binary.Reasoning.Setoid as ≈-Reasoning

------------------------------------------------------------------------
-- If f and g are mutually inverse maps between A and B, g is congruent,
-- f is a homomorphism, then g is a homomorphism.

module _ {α α= β β=} (M₁ : Magma α α=) (M₂ : Magma β β=) where

  private
    open module M₁ = Magma M₁ using () renaming (_≈_ to _≈₁_; _∙_ to _∙₁_)
    open module M₂ = Magma M₂ using () renaming (_≈_ to _≈₂_; _∙_ to _∙₂_)

  homomorphic₂-inj  : ∀ {f g} → Injective _≈₁_ _≈₂_ f →
                      Inverseˡ _≈₁_ _≈₂_ f g →
                      Homomorphic₂ _ _ _≈₂_ f _∙₁_ _∙₂_  →
                      Homomorphic₂ _ _ _≈₁_ g _∙₂_ _∙₁_
  homomorphic₂-inj {f} {g} inj invˡ homo x y = inj (begin
    f (g (x ∙₂ y))      ≈⟨ invˡ M₁.refl ⟩
    x ∙₂ y              ≈⟨ M₂.∙-cong (invˡ M₁.refl) (invˡ M₁.refl) ⟨
    f (g x) ∙₂ f (g y)  ≈⟨ homo (g x) (g y) ⟨
    f (g x ∙₁ g y)      ∎)
    where open ≈-Reasoning M₂.setoid

  homomorphic₂-inv  : ∀ {f g} → Inverseᵇ _≈₁_ _≈₂_ f g →
                      Homomorphic₂ _ _ _≈₂_ f _∙₁_ _∙₂_  →
                      Homomorphic₂ _ _ _≈₁_ g _∙₂_ _∙₁_
  homomorphic₂-inv {f} {g} (invˡ , invʳ) = homomorphic₂-inj inj invˡ
    where
    inj : Injective _≈₁_ _≈₂_ f
    inj = inverseʳ⇒injective _≈₂_ f M₂.refl M₁.sym M₁.trans invʳ
