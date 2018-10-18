------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the extensional sublist relation over setoid equality.
------------------------------------------------------------------------

open import Relation.Binary hiding (Decidable)

module Data.List.Relation.Subset.Setoid.Properties where

open import Data.Bool using (Bool; true; false)
open import Data.List
open import Data.List.Any using (here; there)
import Data.List.Membership.Setoid as Membership
open import Data.List.Membership.Setoid.Properties
import Data.List.Relation.Subset.Setoid as Sublist
import Data.List.Relation.Equality.Setoid as Equality
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Unary using (Pred; Decidable)
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
    open PreorderReasoning ⊆-preorder public
      renaming (_∼⟨_⟩_ to _⊆⟨_⟩_ ; _≈⟨_⟩_ to _≋⟨_⟩_ ; _≈⟨⟩_ to _≋⟨⟩_)

    infix 1 _∈⟨_⟩_
    _∈⟨_⟩_ : ∀ x {xs ys} → x ∈ xs → xs IsRelatedTo ys → x ∈ ys
    x ∈⟨ x∈xs ⟩ xs⊆ys = (begin xs⊆ys) x∈xs

------------------------------------------------------------------------
-- filter

module _ {a p ℓ} (S : Setoid a ℓ)
         {P : Pred (Carrier S) p} (P? : Decidable P) where

  open Setoid S renaming (Carrier to A)
  open Sublist S

  filter⁺ : ∀ xs → filter P? xs ⊆ xs
  filter⁺ []       ()
  filter⁺ (x ∷ xs) y∈f[x∷xs] with P? x
  ... | no  _ = there (filter⁺ xs y∈f[x∷xs])
  ... | yes _ with y∈f[x∷xs]
  ...   | here  y≈x     = here y≈x
  ...   | there y∈f[xs] = there (filter⁺ xs y∈f[xs])
