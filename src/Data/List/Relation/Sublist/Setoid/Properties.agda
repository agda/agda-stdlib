------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the sublist relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary hiding (Decidable)

module Data.List.Relation.Sublist.Setoid.Properties where

open import Data.Bool using (Bool; true; false)
open import Data.List
open import Data.List.Any using (Any; here; there)
import Data.List.Any.Properties as AnyP
import Data.List.Membership.Setoid as Membership
import Data.List.Membership.Setoid.Properties as MembershipP
open import Data.List.Membership.Setoid.Properties
import Data.List.Relation.Sublist.Setoid as Sublist
import Data.List.Relation.Equality.Setoid as Equality
open import Data.Product as Prod using ()
open import Function using (_∘_; _∘′_; id)
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse as Inv using (_↔_; module Inverse)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Decidable)
open import Relation.Binary.InducedPreorders using (InducedPreorder₂)
import Relation.Binary.PreorderReasoning as PreorderReasoning

open Setoid using (Carrier)

------------------------------------------------------------------------
-- Relational properties

module _ {a ℓ} (S : Setoid a ℓ) where

  open Equality S
  open Sublist S
  open Membership S

  ⊆-reflexive : _≋_ ⇒ _⊆_
  ⊆-reflexive xs≋ys = ∈-resp-≋ S xs≋ys

  ⊆-refl : Reflexive _⊆_
  ⊆-refl x∈xs = x∈xs

  ⊆-trans : Transitive _⊆_
  ⊆-trans xs⊆ys ys⊆zs x∈xs = ys⊆zs (xs⊆ys x∈xs)

  ⊆-isPreorder : IsPreorder _≋_ _⊆_
  ⊆-isPreorder = record
    { isEquivalence = ≋-isEquivalence
    ; reflexive     = ⊆-reflexive
    ; trans         = ⊆-trans
    }

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = record
    { isPreorder = ⊆-isPreorder
    }

  -- Reasoning over subsets
  module ⊆-Reasoning where
    open PreorderReasoning ⊆-preorder public renaming (_∼⟨_⟩_ to _⊆⟨_⟩_)

    infix 1 _∈⟨_⟩_
    _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

------------------------------------------------------------------------
-- filter

module _ {a p ℓ} (S : Setoid a ℓ)
         {P : Carrier S → Set p} (P? : Decidable P) where

  open Setoid S renaming (Carrier to A)
  open Sublist S

  filter⁺ : ∀ xs → filter P? xs ⊆ xs
  filter⁺ []       ()
  filter⁺ (x ∷ xs) y∈f[x∷xs] with P? x
  ... | no  _ = there (filter⁺ xs y∈f[x∷xs])
  ... | yes _ with y∈f[x∷xs]
  ...   | here  y≈x     = here y≈x
  ...   | there y∈f[xs] = there (filter⁺ xs y∈f[xs])

------------------------------------------------------------------------
-- DEPRECATED
------------------------------------------------------------------------
-- Please use `filter` instead of `boolFilter`

module _ {a ℓ} (S : Setoid a ℓ) (p : Setoid.Carrier S → Bool) where

  open Setoid S renaming (Carrier to A)
  open Sublist S

  boolFilter-⊆ : ∀ xs → boolFilter p xs ⊆ xs
  boolFilter-⊆ []       ()
  boolFilter-⊆ (x ∷ xs) y∈f[x∷xs] with p x
  ... | false = there (boolFilter-⊆ xs y∈f[x∷xs])
  ... | true  with y∈f[x∷xs]
  ...   | here  y≈x     = here y≈x
  ...   | there y∈f[xs] = there (boolFilter-⊆ xs y∈f[xs])
