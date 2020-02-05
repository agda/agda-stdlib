------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the extensional sublist relation over setoid equality.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary hiding (Decidable)

module Data.List.Relation.Binary.Subset.Setoid.Properties where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base
open import Data.List.Relation.Unary.Any using (here; there)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
import Data.List.Relation.Binary.Subset.Setoid as Sublist
import Data.List.Relation.Binary.Equality.Setoid as Equality
open import Relation.Nullary using (¬_; does)
open import Relation.Unary using (Pred; Decidable)
import Relation.Binary.Reasoning.Preorder as PreorderReasoning

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
    private
      module Base = PreorderReasoning ⊆-preorder

    open Base public
      hiding (step-∼; step-≈; step-≈˘)
      renaming (_≈⟨⟩_ to _≋⟨⟩_)

    infix 2 step-⊆ step-≋ step-≋˘
    infix 1 step-∈

    step-∈ : ∀ x {xs ys} → xs IsRelatedTo ys → x ∈ xs → x ∈ ys
    step-∈ x xs⊆ys x∈xs = (begin xs⊆ys) x∈xs

    step-⊆  = Base.step-∼
    step-≋  = Base.step-≈
    step-≋˘ = Base.step-≈˘

    syntax step-∈  x  xs⊆ys x∈xs  = x  ∈⟨  x∈xs  ⟩ xs⊆ys
    syntax step-⊆  xs ys⊆zs xs⊆ys = xs ⊆⟨  xs⊆ys ⟩ ys⊆zs
    syntax step-≋  xs ys⊆zs xs≋ys = xs ≋⟨  xs≋ys ⟩ ys⊆zs
    syntax step-≋˘ xs ys⊆zs xs≋ys = xs ≋˘⟨ xs≋ys ⟩ ys⊆zs

------------------------------------------------------------------------
-- filter

module _ {a p ℓ} (S : Setoid a ℓ)
         {P : Pred (Carrier S) p} (P? : Decidable P) where

  open Setoid S renaming (Carrier to A)
  open Sublist S

  filter⁺ : ∀ xs → filter P? xs ⊆ xs
  filter⁺ (x ∷ xs) y∈f[x∷xs] with does (P? x)
  ... | false = there (filter⁺ xs y∈f[x∷xs])
  ... | true  with y∈f[x∷xs]
  ...   | here  y≈x     = here y≈x
  ...   | there y∈f[xs] = there (filter⁺ xs y∈f[xs])
