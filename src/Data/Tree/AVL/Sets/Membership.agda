------------------------------------------------------------------------
-- The Agda standard library
--
-- Membership relation for AVL sets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (StrictTotalOrder)

module Data.Tree.AVL.Sets.Membership
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (true; false)
open import Data.Product as Prod using (_,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_; _∘′_; const)

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no; Reflects)
open import Relation.Nullary.Reflects using (fromEquivalence)

open StrictTotalOrder strictTotalOrder renaming (Carrier to A)
open import Data.Tree.AVL.Sets strictTotalOrder
import Data.Tree.AVL.Map.Membership strictTotalOrder as Map
open import Data.Tree.AVL.Map.Relation.Unary.Any strictTotalOrder as Mapₚ

private
  variable
    x y : A
    s : ⟨Set⟩

infix 4 _∈_

------------------------------------------------------------------------
-- ∈

_∈_ : A → ⟨Set⟩ → Set _
x ∈ s = Any ((x ≈_) ∘ proj₁) s

_∉_ : A → ⟨Set⟩ → Set _
x ∉ s = ¬ x ∈ s

∈toMap : x ∈ s → (x , tt) Map.∈ s
∈toMap = Mapₚ.map (_, refl)

∈fromMap : (x , tt) Map.∈ s → x ∈ s
∈fromMap = Mapₚ.map proj₁

------------------------------------------------------------------------
-- empty

∈-empty : x ∉ empty
∈-empty = Map.∈-empty ∘ ∈toMap

------------------------------------------------------------------------
-- singleton

∈-singleton⁺ : x ∈ singleton x
∈-singleton⁺ = ∈fromMap Map.∈-singleton⁺

∈-singleton⁻ : x ∈ singleton y → x ≈ y
∈-singleton⁻ p = proj₁ (Map.∈-singleton⁻ (∈toMap p))

------------------------------------------------------------------------
-- insert

∈-insert⁺ : x ∈ s → x ∈ insert y s
∈-insert⁺ {x = x} {s = s} {y = y} x∈s with x ≟ y
... | yes x≈y = ∈fromMap (Map.∈-Respectsˡ (Eq.sym x≈y , refl) Map.∈-insert⁺⁺)
... | no x≉y = ∈fromMap (Map.∈-insert⁺ x≉y (∈toMap x∈s))

∈-insert⁺⁺ : x ∈ insert x s
∈-insert⁺⁺ = ∈fromMap Map.∈-insert⁺⁺

∈-insert⁻ : x ∈ insert y s → x ≈ y ⊎ x ∈ s
∈-insert⁻ = Sum.map proj₁ (∈fromMap ∘ proj₂) ∘ Map.∈-insert⁻ ∘ ∈toMap

------------------------------------------------------------------------
-- ∈?

∈-∈? : x ∈ s → (x ∈? s) ≡ true
∈-∈? = Map.∈-∈? ∘′ ∈toMap

∉-∈? : x ∉ s → (x ∈? s) ≡ false
∉-∈? x∉s = Map.∉-∈? (const (x∉s ∘ ∈fromMap))

∈?-∈ : (x ∈? s) ≡ true → x ∈ s
∈?-∈ = ∈fromMap ∘′ proj₂ ∘′ Map.∈?-∈

∈?-∉ : (x ∈? s) ≡ false → x ∉ s
∈?-∉ p = Map.∈?-∉ p tt ∘ ∈toMap

∈?-Reflects-∈ : Reflects (x ∈ s) (x ∈? s)
∈?-Reflects-∈ {x = x} {s = s} with x ∈? s in eq
... | true = Reflects.ofʸ (∈?-∈ eq)
... | false = Reflects.ofⁿ (∈?-∉ eq)
