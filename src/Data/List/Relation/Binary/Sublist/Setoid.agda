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

open Setoid S renaming (Carrier to A)
open SetoidEquality S

------------------------------------------------------------------------
-- Definition

infix 4 _⊆_
_⊆_ : Rel (List A) (c ⊔ ℓ)
_⊆_ = Heterogeneous.Sublist _≈_

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

⊆-refl : Reflexive _⊆_
⊆-refl = HeterogeneousProperties.refl refl

⊆-trans : Transitive _⊆_
⊆-trans = HeterogeneousProperties.trans trans

⊆-antisym : Antisymmetric _≋_ _⊆_
⊆-antisym = HeterogeneousProperties.antisym (λ x≈y _ → x≈y)

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
