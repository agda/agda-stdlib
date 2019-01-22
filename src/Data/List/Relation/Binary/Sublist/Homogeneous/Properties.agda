-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the homogeneous sublist relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Sublist.Homogeneous.Properties where

open import Data.List.Base
open import Data.List.Relation.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Binary.Sublist.Heterogeneous
open import Data.List.Relation.Binary.Sublist.Heterogeneous.Properties public
import Data.List.Relation.Binary.Pointwise as Pw
open import Data.Nat.Base using (zero; suc)

open import Function
open import Relation.Unary as U using (Pred)
open import Relation.Binary
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬?)

module _ {a r} {A : Set a} {R : Rel A r} where

  refl : Reflexive R → Reflexive (Sublist R)
  refl R-refl = fromPointwise (Pw.refl R-refl)

module _ {a e r} {A : Set a} {E : Rel A e} {R : Rel A r} where

  isPreorder : IsPreorder E R → IsPreorder (Pointwise E) (Sublist R)
  isPreorder ER-isPreorder = record
    { isEquivalence = Pw.isEquivalence ER.isEquivalence
    ; reflexive     = fromPointwise ∘ Pw.map ER.reflexive
    ; trans         = trans ER.trans
    } where module ER = IsPreorder ER-isPreorder

  isPartialOrder : IsPartialOrder E R → IsPartialOrder (Pointwise E) (Sublist R)
  isPartialOrder ER-isPartialOrder = record
    { isPreorder = isPreorder ER.isPreorder
    ; antisym    = antisym ER.antisym
    } where module ER = IsPartialOrder ER-isPartialOrder

  isDecPartialOrder : IsDecPartialOrder E R →
    IsDecPartialOrder (Pointwise E) (Sublist R)
  isDecPartialOrder ER-isDecPartialOrder = record
    { isPartialOrder = isPartialOrder ER.isPartialOrder
    ; _≟_            = Pw.decidable ER._≟_
    ; _≤?_           = sublist? ER._≤?_
    } where module ER = IsDecPartialOrder ER-isDecPartialOrder

module _ {a e r} where

  preorder : Preorder a e r → Preorder _ _ _
  preorder ER-preorder = record {
    isPreorder = isPreorder ER.isPreorder
    } where module ER = Preorder ER-preorder

  poset : Poset a e r → Poset _ _ _
  poset ER-poset = record {
    isPartialOrder = isPartialOrder ER.isPartialOrder
    } where module ER = Poset ER-poset

  decPoset : DecPoset a e r → DecPoset _ _ _
  decPoset ER-poset = record {
    isDecPartialOrder = isDecPartialOrder ER.isDecPartialOrder
    } where module ER = DecPoset ER-poset

module _ {a r p} {A : Set a} {R : Rel A r} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-filter : ∀ {as} → Pointwise R as as →
    Sublist R (takeWhile P? as) (filter P? as)
  takeWhile-filter [] = []
  takeWhile-filter {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ takeWhile-filter ps
  ... | no ¬pa = minimum _

  filter-dropWhile : ∀ {as} → Pointwise R as as →
    Sublist R (filter P? as) (dropWhile (¬? ∘ P?) as)
  filter-dropWhile [] = []
  filter-dropWhile {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ filter-Sublist P? (fromPointwise ps)
  ... | no ¬pa = filter-dropWhile ps
