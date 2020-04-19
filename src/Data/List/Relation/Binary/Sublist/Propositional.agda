------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation. This is commonly
-- known as Order Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Propositional
  {a} {A : Set a} where

open import Data.List.Base using (List)
open import Data.List.Relation.Binary.Equality.Propositional using (≋⇒≡)
import Data.List.Relation.Binary.Sublist.Setoid as SetoidSublist
open import Data.List.Relation.Unary.Any using (Any)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Re-export definition and operations from setoid sublists

open SetoidSublist (setoid A) public
  hiding
  (lookup; ⊆-reflexive; ⊆-antisym
  ; ⊆-isPreorder; ⊆-isPartialOrder
  ; ⊆-preorder; ⊆-poset
  )

------------------------------------------------------------------------
-- Additional operations

module _ {p} {P : Pred A p} where

  lookup : ∀ {xs ys} → xs ⊆ ys → Any P xs → Any P ys
  lookup = SetoidSublist.lookup (setoid A) (subst _)

------------------------------------------------------------------------
-- Relational properties

⊆-reflexive : _≡_ ⇒ _⊆_
⊆-reflexive refl = ⊆-refl

⊆-antisym : Antisymmetric _≡_ _⊆_
⊆-antisym xs⊆ys ys⊆xs = ≋⇒≡ (SetoidSublist.⊆-antisym (setoid A) xs⊆ys ys⊆xs)

⊆-isPreorder : IsPreorder _≡_ _⊆_
⊆-isPreorder = record
  { isEquivalence = isEquivalence
  ; reflexive     = ⊆-reflexive
  ; trans         = ⊆-trans
  }

⊆-isPartialOrder : IsPartialOrder _≡_ _⊆_
⊆-isPartialOrder = record
  { isPreorder = ⊆-isPreorder
  ; antisym    = ⊆-antisym
  }

⊆-preorder : Preorder a a a
⊆-preorder = record
  { isPreorder = ⊆-isPreorder
  }

⊆-poset : Poset a a a
⊆-poset = record
  { isPartialOrder = ⊆-isPartialOrder
  }

------------------------------------------------------------------------
-- Separating two sublists
--
-- Two possibly overlapping sublists τ : xs ⊆ zs and σ : ys ⊆ zs
-- can be turned into disjoint lists τρ : xs ⊆ zs and τρ : ys ⊆ zs′
-- by duplicating all entries of zs that occur both in xs and ys,
-- resulting in an extension ρ : zs ⊆ zs′ of zs.

record Separation {xs ys zs} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) : Set a where
  field
    {inflation} : List A
    separator₁  : zs ⊆ inflation
    separator₂  : zs ⊆ inflation
  separated₁ = ⊆-trans τ₁ separator₁
  separated₂ = ⊆-trans τ₂ separator₂
  field
    disjoint    : Disjoint separated₁ separated₂

infixr 5 _∷ₙ-Sep_ _∷ₗ-Sep_ _∷ᵣ-Sep_

-- Empty separation

[]-Sep : Separation [] []
[]-Sep = record { separator₁ = [] ; separator₂ = [] ; disjoint = [] }

-- Weaken a separation

_∷ₙ-Sep_ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
           ∀ z → Separation τ₁ τ₂ → Separation (z ∷ʳ τ₁) (z ∷ʳ τ₂)
z ∷ₙ-Sep record{ separator₁ = ρ₁; separator₂ = ρ₂; disjoint = d } = record
  { separator₁ = refl ∷ ρ₁
  ; separator₂ = refl ∷ ρ₂
  ; disjoint   = z   ∷ₙ d
  }

-- Extend a separation by an element of the first sublist.
--
-- Note: this requires a category law from the underlying equality,
-- trans x=z refl = x=z, thus, separation is not available for Sublist.Setoid.

_∷ₗ-Sep_ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
          ∀ {x z} (x≡z : x ≡ z) → Separation τ₁ τ₂ → Separation (x≡z ∷ τ₁) (z ∷ʳ τ₂)
refl ∷ₗ-Sep record{ separator₁ = ρ₁; separator₂ = ρ₂; disjoint = d } = record
  { separator₁ = refl ∷ ρ₁
  ; separator₂ = refl ∷ ρ₂
  ; disjoint   = refl ∷ₗ d
  }

-- Extend a separation by an element of the second sublist.

_∷ᵣ-Sep_ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
          ∀ {y z} (y≡z : y ≡ z) → Separation τ₁ τ₂ → Separation (z ∷ʳ τ₁) (y≡z ∷ τ₂)
refl ∷ᵣ-Sep record{ separator₁ = ρ₁; separator₂ = ρ₂; disjoint = d } = record
  { separator₁ = refl ∷ ρ₁
  ; separator₂ = refl ∷ ρ₂
  ; disjoint   = refl ∷ᵣ d
  }

-- Extend a separation by a common element of both sublists.
--
-- Left-biased: the left separator gets the first copy
-- of the common element.

∷-Sepˡ : ∀ {xs ys zs} {τ₁ : xs ⊆ zs} {τ₂ : ys ⊆ zs} →
        ∀ {x y z} (x≡z : x ≡ z) (y≡z : y ≡ z) →
        Separation τ₁ τ₂ → Separation (x≡z ∷ τ₁) (y≡z ∷ τ₂)
∷-Sepˡ refl refl record{ separator₁ = ρ₁; separator₂ = ρ₂; disjoint = d } = record
  { separator₁ = _ ∷ʳ refl ∷ ρ₁
  ; separator₂ = refl ∷ _ ∷ʳ ρ₂
  ; disjoint   = refl ∷ᵣ (refl ∷ₗ d)
  }

-- Left-biased separation of two sublists.  Of common elements,
-- the first sublist receives the first copy.

separateˡ : ∀ {xs ys zs} (τ₁ : xs ⊆ zs) (τ₂ : ys ⊆ zs) → Separation τ₁ τ₂
separateˡ [] [] = []-Sep
separateˡ (z  ∷ʳ τ₁) (z  ∷ʳ τ₂) = z   ∷ₙ-Sep separateˡ τ₁ τ₂
separateˡ (z  ∷ʳ τ₁) (y≡z ∷ τ₂) = y≡z ∷ᵣ-Sep separateˡ τ₁ τ₂
separateˡ (x≡z ∷ τ₁) (z  ∷ʳ τ₂) = x≡z ∷ₗ-Sep separateˡ τ₁ τ₂
separateˡ (x≡z ∷ τ₁) (y≡z ∷ τ₂) = ∷-Sepˡ x≡z y≡z (separateˡ τ₁ τ₂)
