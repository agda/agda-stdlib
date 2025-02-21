------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the homogeneous suffix relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Relation.Binary.Suffix.Homogeneous.Properties where

open import Level
open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Structures
  using (IsPreorder; IsPartialOrder; IsDecPartialOrder)

open import Data.List.Relation.Binary.Pointwise as Pointwise using (Pointwise)
open import Data.List.Relation.Binary.Suffix.Heterogeneous
open import Data.List.Relation.Binary.Suffix.Heterogeneous.Properties

private
  variable
    a b r s : Level
    A : Set a
    B : Set b
    R : REL A B r
    S : REL A B s

isPreorder : IsPreorder R S → IsPreorder (Pointwise R) (Suffix S)
isPreorder po = record
  { isEquivalence = Pointwise.isEquivalence PO.isEquivalence
  ; reflexive     = fromPointwise ∘′ Pointwise.map PO.reflexive
  ; trans         = trans PO.trans
  } where module PO = IsPreorder po

isPartialOrder : IsPartialOrder R S → IsPartialOrder (Pointwise R) (Suffix S)
isPartialOrder po = record
  { isPreorder = isPreorder PO.isPreorder
  ; antisym    = antisym PO.antisym
  } where module PO = IsPartialOrder po

isDecPartialOrder : IsDecPartialOrder R S → IsDecPartialOrder (Pointwise R) (Suffix S)
isDecPartialOrder dpo = record
  { isPartialOrder = isPartialOrder DPO.isPartialOrder
  ; _≟_            = Pointwise.decidable DPO._≟_
  ; _≤?_           = suffix? DPO._≤?_
  } where module DPO = IsDecPartialOrder dpo


module _ {A : Set a} where

  open import Data.List.Base using (List; []; _∷_)
  open import Data.List.Properties using (++-monoid)
  open import Algebra.Properties.Monoid.Divisibility (++-monoid A)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
  open import Relation.Binary using (_⇒_)

  Suffix-as-∣ʳ : Suffix _≡_ ⇒ _∣ʳ_
  Suffix-as-∣ʳ (here equal) = ∣ʳ-reflexive (Pointwise.Pointwise-≡⇒≡ equal)
  Suffix-as-∣ʳ (there suff) = x∣ʳy⇒x∣ʳzy (_ ∷ []) (Suffix-as-∣ʳ suff)

  ∣ʳ-as-Suffix : _∣ʳ_ ⇒ Suffix _≡_
  ∣ʳ-as-Suffix (rest , refl) = fromView (rest ++ Pointwise.refl refl)
