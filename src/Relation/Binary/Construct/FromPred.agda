------------------------------------------------------------------------
-- The Agda standard library
--
-- Every respectful unary relation induces a preorder. No claim is
-- made that this preorder is unique.
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Unary using (Pred)

module Relation.Binary.Construct.FromPred
  {s₁ s₂} (S : Setoid s₁ s₂)          -- The underlying equality
  {p} (P : Pred (Setoid.Carrier S) p) -- The predicate
  where

open import Function
open import Data.Product

open module Eq = Setoid S using (_≈_) renaming (Carrier to A)

------------------------------------------------------------------------
-- Definition

Resp : Rel A p
Resp x y = P x → P y

------------------------------------------------------------------------
-- Properties

reflexive : P Respects _≈_ → _≈_ ⇒ Resp
reflexive resp = resp

refl : P Respects _≈_ → Reflexive Resp
refl resp = resp Eq.refl

trans : Transitive Resp
trans x⇒y y⇒z = y⇒z ∘ x⇒y

isPreorder : P Respects _≈_ → IsPreorder _≈_ Resp
isPreorder resp = record
  { isEquivalence = Eq.isEquivalence
  ; reflexive     = reflexive resp
  ; trans         = flip _∘′_
  }

preorder : P Respects _≈_ → Preorder _ _ _
preorder resp = record
  { isPreorder = isPreorder resp
  }
