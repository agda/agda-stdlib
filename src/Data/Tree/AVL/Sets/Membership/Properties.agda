------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of membership for AVL sets
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Bundles using (StrictTotalOrder)

module Data.Tree.AVL.Sets.Membership.Properties
  {a ℓ₁ ℓ₂} (strictTotalOrder : StrictTotalOrder a ℓ₁ ℓ₂)
  where

open import Data.Bool.Base using (true; false)
open import Data.Product.Base as Product using (_,_; proj₁; proj₂)
open import Data.Sum.Base as Sum using (_⊎_)
open import Data.Unit.Base using (tt)
open import Function.Base using (_∘_; _∘′_; const)

open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no; Reflects)
open import Relation.Nullary.Reflects using (fromEquivalence)

open StrictTotalOrder strictTotalOrder renaming (Carrier to A)
open import Data.Tree.AVL.Sets strictTotalOrder
open import Data.Tree.AVL.Sets.Membership strictTotalOrder
open import Data.Tree.AVL.Map.Membership.Propositional strictTotalOrder using (_∈ₖᵥ_)
import Data.Tree.AVL.Map.Membership.Propositional.Properties strictTotalOrder as Map
open import Data.Tree.AVL.Map.Relation.Unary.Any strictTotalOrder as Mapₚ

private
  variable
    x y : A
    s : ⟨Set⟩

∈toMap : x ∈ s → (x , tt) ∈ₖᵥ s
∈toMap = Mapₚ.map (_, refl)

∈fromMap : (x , tt) ∈ₖᵥ s → x ∈ s
∈fromMap = Mapₚ.map proj₁

------------------------------------------------------------------------
-- empty

∈-empty : x ∉ empty
∈-empty = Map.∈ₖᵥ-empty ∘ ∈toMap

------------------------------------------------------------------------
-- singleton

∈-singleton⁺ : x ∈ singleton x
∈-singleton⁺ = ∈fromMap Map.∈ₖᵥ-singleton⁺

∈-singleton⁻ : x ∈ singleton y → x ≈ y
∈-singleton⁻ p = proj₁ (Map.∈ₖᵥ-singleton⁻ (∈toMap p))

------------------------------------------------------------------------
-- insert

∈-insert⁺ : x ∈ s → x ∈ insert y s
∈-insert⁺ {x = x} {s = s} {y = y} x∈s with x ≟ y
... | yes x≈y = ∈fromMap (Map.∈ₖᵥ-Respectsˡ (Eq.sym x≈y , refl) Map.∈ₖᵥ-insert⁺⁺)
... | no x≉y = ∈fromMap (Map.∈ₖᵥ-insert⁺ x≉y (∈toMap x∈s))

∈-insert⁺⁺ : x ∈ insert x s
∈-insert⁺⁺ = ∈fromMap Map.∈ₖᵥ-insert⁺⁺

∈-insert⁻ : x ∈ insert y s → x ≈ y ⊎ x ∈ s
∈-insert⁻ = Sum.map proj₁ (∈fromMap ∘ proj₂) ∘ Map.∈ₖᵥ-insert⁻ ∘ ∈toMap

------------------------------------------------------------------------
-- member

∈-member : x ∈ s → member x s ≡ true
∈-member = Map.∈ₖᵥ-member ∘′ ∈toMap

∉-member : x ∉ s → member x s ≡ false
∉-member x∉s = Map.∉ₖᵥ-member (const (x∉s ∘ ∈fromMap))

member-∈ : member x s ≡ true → x ∈ s
member-∈ = ∈fromMap ∘′ proj₂ ∘′ Map.member-∈ₖᵥ

member-∉ : member x s ≡ false → x ∉ s
member-∉ p = Map.member-∉ₖᵥ p tt ∘ ∈toMap

member-Reflects-∈ : Reflects (x ∈ s) (member x s)
member-Reflects-∈ {x = x} {s = s} with member x s in eq
... | true = Reflects.ofʸ (member-∈ eq)
... | false = Reflects.ofⁿ (member-∉ eq)
