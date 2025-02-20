------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the homogeneous prefix relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Prefix.Homogeneous.Properties where

open import Level
open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (Rel; REL; _⇒_)
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsDecPartialOrder)

open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Prefix.Heterogeneous
open import Data.List.Relation.Binary.Prefix.Heterogeneous.Properties


private
  variable
    a b r s : Level
    A : Set a
    B : Set b
    R : REL A B r
    S : REL A B s

isPreorder : IsPreorder R S → IsPreorder (Pointwise R) (Prefix S)
isPreorder po = record
  { isEquivalence = Pointwise.isEquivalence PO.isEquivalence
  ; reflexive     = fromPointwise ∘′ Pointwise.map PO.reflexive
  ; trans         = trans PO.trans
  } where module PO = IsPreorder po

isPartialOrder : IsPartialOrder R S → IsPartialOrder (Pointwise R) (Prefix S)
isPartialOrder po = record
  { isPreorder = isPreorder PO.isPreorder
  ; antisym    = antisym PO.antisym
  } where module PO = IsPartialOrder po

isDecPartialOrder : IsDecPartialOrder R S → IsDecPartialOrder (Pointwise R) (Prefix S)
isDecPartialOrder dpo = record
  { isPartialOrder = isPartialOrder DPO.isPartialOrder
  ; _≟_            = Pointwise.decidable DPO._≟_
  ; _≤?_           = prefix? DPO._≤?_
  } where module DPO = IsDecPartialOrder dpo



module _ {A : Set a} where

  open import Data.List.Base using (List; []; _∷_)
  open import Data.List.Properties using (++-monoid)
  open import Algebra.Properties.Monoid.Divisibility (++-monoid A)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Binary using (_⇒_)

  Prefix-as-∣ˡ : Prefix _≡_ ⇒ _∣ˡ_
  Prefix-as-∣ˡ []          = ε∣ˡ _
  Prefix-as-∣ˡ (refl ∷ tl) = x∣ˡy⇒zx∣ˡzy (_ ∷ []) (Prefix-as-∣ˡ tl)

  ∣ˡ-as-Prefix : _∣ˡ_ ⇒ Prefix _≡_
  ∣ˡ-as-Prefix (rest , refl) = fromView (Pointwise.refl refl ++ rest)
