-----------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of the homogeneous sublist relation
------------------------------------------------------------------------

module Data.List.Relation.Sublist.Homogeneous.Properties where

open import Data.List.Base using (List; []; _∷_; takeWhile; dropWhile; filter)
open import Data.List.Relation.Pointwise as Pw using (Pointwise; []; _∷_)
open import Data.List.Relation.Sublist.Heterogeneous
open import Data.List.Relation.Sublist.Heterogeneous.Properties public

open import Function
open import Relation.Unary as U using (Pred)
open import Relation.Binary
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Negation using (¬?)

module _ {a r} {A : Set a} {R : Rel A r} where

  Sublist-refl : Reflexive R → Reflexive (Sublist R)
  Sublist-refl R-refl {[]}      = []
  Sublist-refl R-refl {x ∷ xs}  = R-refl ∷ Sublist-refl R-refl

module _ {a e r} {A : Set a} {E : Rel A e} {R : Rel A r} where

  Sublist-isPreorder : IsPreorder E R → IsPreorder (Pointwise E) (Sublist R)
  Sublist-isPreorder ER-isPreorder = record
    { isEquivalence = Pw.isEquivalence ER.isEquivalence
    ; reflexive     = fromPointwise ∘ Pw.map ER.reflexive
    ; trans         = trans ER.trans
    } where module ER = IsPreorder ER-isPreorder

  Sublist-isPartialOrder : IsPartialOrder E R → IsPartialOrder (Pointwise E) (Sublist R)
  Sublist-isPartialOrder ER-isPartialOrder = record
    { isPreorder = Sublist-isPreorder ER.isPreorder
    ; antisym    = antisym ER.antisym
    } where module ER = IsPartialOrder ER-isPartialOrder

  Sublist-isDecPartialOrder : IsDecPartialOrder E R →
    IsDecPartialOrder (Pointwise E) (Sublist R)
  Sublist-isDecPartialOrder ER-isDecPartialOrder = record
    { isPartialOrder = Sublist-isPartialOrder ER.isPartialOrder
    ; _≟_            = Pw.decidable ER._≟_
    ; _≤?_           = sublist? ER._≤?_
    } where module ER = IsDecPartialOrder ER-isDecPartialOrder

module _ {a e r} where

  Sublist-preorder : Preorder a e r → Preorder _ _ _
  Sublist-preorder ER-preorder = record {
    isPreorder = Sublist-isPreorder ER.isPreorder
    } where module ER = Preorder ER-preorder

  Sublist-poset : Poset a e r → Poset _ _ _
  Sublist-poset ER-poset = record {
    isPartialOrder = Sublist-isPartialOrder ER.isPartialOrder
    } where module ER = Poset ER-poset

  Sublist-decPoset : DecPoset a e r → DecPoset _ _ _
  Sublist-decPoset ER-poset = record {
    isDecPartialOrder = Sublist-isDecPartialOrder ER.isDecPartialOrder
    } where module ER = DecPoset ER-poset

module _ {a r p} {A : Set a} {R : Rel A r} {P : Pred A p} (P? : U.Decidable P) where

  takeWhile-Sublist-filter : ∀ {as} → Pointwise R as as →
    Sublist R (takeWhile P? as) (filter P? as)
  takeWhile-Sublist-filter [] = []
  takeWhile-Sublist-filter {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ takeWhile-Sublist-filter ps
  ... | no ¬pa = minimum _

  filter-Sublist-dropWhile : ∀ {as} → Pointwise R as as →
    Sublist R (filter P? as) (dropWhile (¬? ∘ P?) as)
  filter-Sublist-dropWhile [] = []
  filter-Sublist-dropWhile {a ∷ as} (p ∷ ps) with P? a
  ... | yes pa = p ∷ filter-Sublist P? ps
  ... | no ¬pa = filter-Sublist-dropWhile ps
