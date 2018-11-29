------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the heterogeneous suffix relation
------------------------------------------------------------------------

module Data.List.Relation.Suffix.Heterogeneous where

open import Level
open import Relation.Binary using (REL; _⇒_)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise as Pointwise using (Pointwise; []; _∷_)

module _ {a b r} {A : Set a} {B : Set b} (R : REL A B r) where

  data Suffix : REL (List A) (List B) (a ⊔ b ⊔ r) where
    here  : ∀ {as bs} → Pointwise R as bs → Suffix as bs
    there : ∀ {b as bs} → Suffix as bs → Suffix as (b ∷ bs)

  data SuffixView (as : List A) : List B → Set (a ⊔ b ⊔ r) where
    _++_ : ∀ cs {ds} → Pointwise R as ds → SuffixView as (cs List.++ ds)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  tail : ∀ {a as bs} → Suffix R (a ∷ as) bs → Suffix R as bs
  tail (here (_ ∷ rs)) = there (here rs)
  tail (there x) = there (tail x)

module _ {a b r s} {A : Set a} {B : Set b} {R : REL A B r} {S : REL A B s} where

  map : R ⇒ S → Suffix R ⇒ Suffix S
  map R⇒S (here rs)   = here (Pointwise.map R⇒S rs)
  map R⇒S (there suf) = there (map R⇒S suf)

module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  toView : ∀ {as bs} → Suffix R as bs → SuffixView R as bs
  toView (here rs) = [] ++ rs
  toView (there {c} suf) with toView suf
  ... | cs ++ rs = (c ∷ cs) ++ rs

  fromView : ∀ {as bs} → SuffixView R as bs → Suffix R as bs
  fromView ([]       ++ rs) = here rs
  fromView ((c ∷ cs) ++ rs) = there (fromView (cs ++ rs))
