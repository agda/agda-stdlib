------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the sublist relation with respect to a
-- setoid. This is a generalisation of what is commonly known as Order
-- Preserving Embeddings (OPE).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid; Rel)

module Data.List.Relation.Binary.Sublist.Setoid
  {c ℓ} (S : Setoid c ℓ) where

open import Level using (_⊔_)
open import Data.List.Base using (List; []; _∷_)
import Data.List.Relation.Binary.Equality.Setoid as SetoidEquality
import Data.List.Relation.Binary.Sublist.Heterogeneous as Heterogeneous
import Data.List.Relation.Binary.Sublist.Heterogeneous.Core
  as HeterogeneousCore
import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties
  as HeterogeneousProperties
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary using (¬_)

open Setoid S renaming (Carrier to A)
open SetoidEquality S

------------------------------------------------------------------------
-- Definition

infix 4 _⊆_ _⊇_ _⊈_ _⊉_

_⊆_ : Rel (List A) (c ⊔ ℓ)
_⊆_ = Heterogeneous.Sublist _≈_

_⊇_ : Rel (List A) (c ⊔ ℓ)
xs ⊇ ys = ys ⊆ xs

_⊈_ : Rel (List A) (c ⊔ ℓ)
xs ⊈ ys = ¬ (xs ⊆ ys)

_⊉_ : Rel (List A) (c ⊔ ℓ)
xs ⊉ ys = ¬ (xs ⊇ ys)

------------------------------------------------------------------------
-- Re-export definitions and operations from heterogeneous sublists

open HeterogeneousCore _≈_ using ([]; _∷_; _∷ʳ_) public
open Heterogeneous {R = _≈_} hiding (Sublist; []; _∷_; _∷ʳ_) public
  renaming
  (toAny to to∈; fromAny to from∈)

------------------------------------------------------------------------
-- Relational properties holding for Setoid case

⊆-reflexive : _≋_ ⇒ _⊆_
⊆-reflexive = HeterogeneousProperties.fromPointwise

open HeterogeneousProperties.Reflexivity {R = _≈_} refl public using ()
  renaming (refl to ⊆-refl)  -- ⊆-refl : Reflexive _⊆_

open HeterogeneousProperties.Transitivity {R = _≈_} {S = _≈_} {T = _≈_} trans public using ()
  renaming (trans to ⊆-trans)  -- ⊆-trans : Transitive _⊆_

open HeterogeneousProperties.Antisymmetry {R = _≈_} {S = _≈_} (λ x≈y _ → x≈y) public using ()
  renaming (antisym to ⊆-antisym)  -- ⊆-antisym : Antisymmetric _≋_ _⊆_

⊆-isPreorder : IsPreorder _≋_ _⊆_
⊆-isPreorder = record
  { isEquivalence = ≋-isEquivalence
  ; reflexive     = ⊆-reflexive
  ; trans         = ⊆-trans
  }

⊆-isPartialOrder : IsPartialOrder _≋_ _⊆_
⊆-isPartialOrder = record
  { isPreorder = ⊆-isPreorder
  ; antisym    = ⊆-antisym
  }

⊆-preorder : Preorder c (c ⊔ ℓ) (c ⊔ ℓ)
⊆-preorder = record
  { isPreorder = ⊆-isPreorder
  }

⊆-poset : Poset c (c ⊔ ℓ) (c ⊔ ℓ)
⊆-poset = record
  { isPartialOrder = ⊆-isPartialOrder
  }

------------------------------------------------------------------------
-- Raw pushout
--
-- The category _⊆_ does not have proper pushouts.  For instance consider:
--
--   τᵤ : [] ⊆ (u ∷ [])
--   τᵥ : [] ⊆ (v ∷ [])
--
-- Then, there are two unrelated upper bounds (u ∷ v ∷ []) and (v ∷ u ∷ []),
-- since _⊆_ does not include permutations.
--
-- Even though there are no unique least upper bounds, we can merge two
-- extensions of a list, producing a minimial superlist of both.
--
-- For the example, the left-biased merge would produce the pair:
--
--   τᵤ′ : (u ∷ []) ⊆ (u ∷ v ∷ [])
--   τᵥ′ : (v ∷ []) ⊆ (u ∷ v ∷ [])
--
-- We call such a pair a raw pushout.  It is then a weak pushout if the
-- resulting square commutes, i.e.:
--
--   ⊆-trans τᵤ τᵤ′ ~ ⊆-trans τᵥ τᵥ′
--
-- This requires a notion of equality _~_ on sublist morphisms.
--
-- Further, commutation requires a similar commutation property
-- for the underlying equality _≈_, namely
--
--   trans x≈y (sym x≈y) == trans x≈z (sym x≈z)
--
-- for some notion of equality _==_ for equality proofs _≈_.
-- Such a property is given e.g. if _≈_ is proof irrelevant
-- or forms a groupoid.

private
  variable
    x y z    : A
    xs ys zs : List A
    τ σ      : xs ⊆ ys

record RawPushout (τ : xs ⊆ ys) (σ : xs ⊆ zs) : Set (c ⊔ ℓ) where
  field
    {upperBound} : List A
    leg₁         : ys ⊆ upperBound
    leg₂         : zs ⊆ upperBound

open RawPushout

------------------------------------------------------------------------
-- Extending corners of a raw pushout square

-- Extending the right upper corner.

_∷ʳ₁_ : ∀ y → RawPushout τ σ → RawPushout (y ∷ʳ τ) σ
y ∷ʳ₁ rpo = record
  { leg₁ = refl ∷ leg₁ rpo
  ; leg₂ = y   ∷ʳ leg₂ rpo
  }

-- Extending the left lower corner.

_∷ʳ₂_ : ∀ z → RawPushout τ σ → RawPushout τ (z ∷ʳ σ)
z ∷ʳ₂ rpo = record
  { leg₁ = z   ∷ʳ leg₁ rpo
  ; leg₂ = refl ∷ leg₂ rpo
  }

-- Extending both of these corners with equal elements.

∷-rpo : (x≈y : x ≈ y) (x≈z : x ≈ z) → RawPushout τ σ → RawPushout (x≈y ∷ τ) (x≈z ∷ σ)
∷-rpo x≈y x≈z rpo = record
  { leg₁ = sym x≈y ∷ leg₁ rpo
  ; leg₂ = sym x≈z ∷ leg₂ rpo
  }

------------------------------------------------------------------------
-- Left-biased pushout: add elements of left extension first.

⊆-joinˡ : (τ : xs ⊆ ys) (σ : xs ⊆ zs) → RawPushout τ σ
⊆-joinˡ []        σ         = record { leg₁ = σ ; leg₂ = ⊆-refl }
⊆-joinˡ (y  ∷ʳ τ) σ         = y ∷ʳ₁ ⊆-joinˡ τ σ
⊆-joinˡ τ@(_ ∷ _) (z  ∷ʳ σ) = z ∷ʳ₂ ⊆-joinˡ τ σ
⊆-joinˡ (x≈y ∷ τ) (x≈z ∷ σ) = ∷-rpo x≈y x≈z (⊆-joinˡ τ σ)
