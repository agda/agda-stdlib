------------------------------------------------------------------------
-- The Agda standard library
--
-- Every respectful unary relation induces a preorder. No claim is
-- made that this preorder is unique.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Bundles using (Setoid; Preorder)
open import Relation.Binary.Structures using (IsPreorder)
open import Relation.Binary.Definitions using (_Respects_; Refl; Reflexive; Transitive)
open import Relation.Unary using (Pred)

module Relation.Binary.Construct.FromPred
  {s₁ s₂} (S : Setoid s₁ s₂)          -- The underlying equality
  {p} (P : Pred (Setoid.Carrier S) p) -- The predicate
  where

open import Function.Base using (_∘_)

open module Eq = Setoid S using (_≈_) renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

Resp : Rel A p
Resp x y = P x → P y

------------------------------------------------------------------------
-- Properties

reflexive : P Respects _≈_ → Refl _≈_ Resp
reflexive resp = resp

refl : P Respects _≈_ → Reflexive Resp
refl resp = resp Eq.refl

trans : Transitive Resp
trans x⇒y y⇒z = y⇒z ∘ x⇒y

isPreorder : P Respects _≈_ → IsPreorder _≈_ Resp
isPreorder resp = record
  { isEquivalence = Eq.isEquivalence
  ; reflexive     = reflexive resp
  ; trans         = trans
  }

preorder : P Respects _≈_ → Preorder _ _ _
preorder resp = record
  { isPreorder = isPreorder resp
  }
