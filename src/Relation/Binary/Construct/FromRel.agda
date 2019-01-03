------------------------------------------------------------------------
-- The Agda standard library
--
-- Every respectful binary relation induces a preorder. No claim is
-- made that this preorder is unique.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary
open Setoid using (Carrier)

module Relation.Binary.Construct.FromRel
  {s₁ s₂} (S : Setoid s₁ s₂)                    -- The underlying equality
  {a r} {A : Set a} (_R_ : REL A (Carrier S) r) -- The relation
  where

open import Data.Product
open import Function
open import Level using (_⊔_)

open module Eq = Setoid S using (_≈_) renaming (Carrier to B)

------------------------------------------------------------------------
-- Definition

Resp : Rel B (a ⊔ r)
Resp x y = ∀ {a} → a R x → a R y

------------------------------------------------------------------------
-- Properties

reflexive : (∀ {a} → (a R_) Respects _≈_) → _≈_ ⇒ Resp
reflexive resp x≈y = resp x≈y

trans : Transitive Resp
trans x∼y y∼z = y∼z ∘ x∼y

isPreorder : (∀ {a} → (a R_) Respects _≈_) → IsPreorder _≈_ Resp
isPreorder resp = record
  { isEquivalence = Eq.isEquivalence
  ; reflexive     = reflexive resp
  ; trans         = trans
  }

preorder : (∀ {a} → (a R_) Respects _≈_) → Preorder _ _ _
preorder resp = record
  { isPreorder = isPreorder resp
  }
