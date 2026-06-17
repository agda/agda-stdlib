------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of disjoint lists (propositional equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Disjoint.Propositional.Properties where


open import Data.List.Base using (List; []; _∷_; concat; deduplicate)
open import Data.List.Relation.Binary.Disjoint.Propositional using (Disjoint)
import Data.List.Relation.Unary.Any as Any using (Any)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product.Base as Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_)
open import Level using (Level)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Symmetric; DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Nullary.Negation using (¬_)

import Data.List.Relation.Binary.Disjoint.Setoid.Properties as S

module _ {a} {A : Set a} where

  private
    Sᴬ = setoid A
    variable
      x : A
      xs ys vs : List A
      xss : List (List A)

  ------------------------------------------------------------------------
  -- Relational properties
  ------------------------------------------------------------------------

  sym : Symmetric Disjoint
  sym = S.sym Sᴬ

  ------------------------------------------------------------------------
  -- Relationship with other predicates
  ------------------------------------------------------------------------

  Disjoint⇒AllAll : Disjoint xs ys → All (λ x → All (λ y → ¬ x ≡ y) ys) xs
  Disjoint⇒AllAll = S.Disjoint⇒AllAll Sᴬ

  ------------------------------------------------------------------------
  -- Introduction (⁺) and elimination (⁻) rules for list operations
  ------------------------------------------------------------------------
  -- concat

  concat⁺ʳ : All (Disjoint vs) xss → Disjoint vs (concat xss)
  concat⁺ʳ = S.concat⁺ʳ (setoid _)

  -- deduplicate
  module _ (_≡?_ : DecidableEquality A) where
    deduplicate⁺ : Disjoint xs ys → Disjoint (deduplicate _≡?_ xs) (deduplicate _≡?_ ys)
    deduplicate⁺ = S.deduplicate⁺ Sᴬ _≡?_
