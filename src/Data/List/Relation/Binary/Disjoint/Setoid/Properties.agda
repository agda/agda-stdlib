------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of disjoint lists (setoid equality)
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Disjoint.Setoid.Properties where

open import Function.Base using (_∘_)
open import Function.Bundles using (_⇔_; mk⇔)
open import Data.List.Base
open import Data.List.Relation.Binary.Disjoint.Setoid
import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
import Data.List.Membership.Setoid.Properties as Mem
open import Data.Product.Base as Product using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Definitions using (Symmetric; DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary.Negation using (¬_)

module _ {c ℓ} (S : Setoid c ℓ) where

  open Setoid S using (_≉_; reflexive) renaming (Carrier to A)

  ------------------------------------------------------------------------
  -- Relational properties
  ------------------------------------------------------------------------

  sym : Symmetric (Disjoint S)
  sym xs#ys (v∈ys , v∈xs) = xs#ys (v∈xs , v∈ys)

  ------------------------------------------------------------------------
  -- Relationship with other predicates
  ------------------------------------------------------------------------

  Disjoint⇒AllAll : ∀ {xs ys} → Disjoint S xs ys →
                    All (λ x → All (x ≉_) ys) xs
  Disjoint⇒AllAll xs#ys = All.map (¬Any⇒All¬ _)
    (All.tabulate (λ v∈xs v∈ys → xs#ys (Any.map reflexive v∈xs , v∈ys)))

  ------------------------------------------------------------------------
  -- Introduction (⁺) and elimination (⁻) rules for list operations
  ------------------------------------------------------------------------
  -- concat

  concat⁺ʳ : ∀ {vs xss} → All (Disjoint S vs) xss → Disjoint S vs (concat xss)
  concat⁺ʳ {xss = xs ∷ xss} (vs#xs ∷ vs#xss) (v∈vs , v∈xs++concatxss)
    with ++⁻ xs v∈xs++concatxss
  ... | inj₁ v∈xs  = vs#xs (v∈vs , v∈xs)
  ... | inj₂ v∈xss = concat⁺ʳ vs#xss (v∈vs , v∈xss)

  -- deduplicate
  module _ (_≟_ : DecidableEquality A) where

    deduplicate⁺ : ∀ {xs ys} → Disjoint S xs ys →
                   Disjoint S (deduplicate _≟_ xs) (deduplicate _≟_ ys)
    deduplicate⁺ = let ∈-dedup⁻ = Mem.∈-deduplicate⁻ S _≟_ in
      _∘ Product.map (∈-dedup⁻ _) (∈-dedup⁻ _)
