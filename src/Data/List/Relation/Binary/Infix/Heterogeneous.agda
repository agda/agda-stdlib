------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the heterogeneous infix relation
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Binary.Infix.Heterogeneous where

open import Level
open import Relation.Binary using (REL; _⇒_)
open import Data.List.Base as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Pointwise
  using (Pointwise)
open import Data.List.Relation.Binary.Prefix.Heterogeneous
  as Prefix using (Prefix; []; _∷_; _++ᵖ_)

private
  variable
    a b r s : Level
    A : Set a
    B : Set b
    R : REL A B r
    S : REL A B s

module _ {A : Set a} {B : Set b} (R : REL A B r) where

  data Infix : REL (List A) (List B) (a ⊔ b ⊔ r) where
    here  : ∀ {as bs}   → Prefix R as bs → Infix as bs
    there : ∀ {b as bs} → Infix as bs → Infix as (b ∷ bs)

  data View (as : List A) : List B → Set (a ⊔ b ⊔ r) where
    MkView : ∀ pref {inf} → Pointwise R as inf → ∀ suff →
            View as (pref List.++ inf List.++ suff)

infixr 5 _++ⁱ_ _ⁱ++_

_++ⁱ_ : ∀ xs {as bs} → Infix R as bs → Infix R as (xs ++ bs)
[]       ++ⁱ rs = rs
(x ∷ xs) ++ⁱ rs = there (xs ++ⁱ rs)

_ⁱ++_ : ∀ {as bs} → Infix R as bs → ∀ xs → Infix R as (bs ++ xs)
here  rs ⁱ++ xs = here (rs ++ᵖ xs)
there rs ⁱ++ xs = there (rs ⁱ++ xs)

map : R ⇒ S → Infix R ⇒ Infix S
map R⇒S (here pref) = here (Prefix.map R⇒S pref)
map R⇒S (there inf) = there (map R⇒S inf)

toView : ∀ {as bs} → Infix R as bs → View R as bs
toView (here p) with Prefix.toView p
...| inf Prefix.++ suff = MkView [] inf suff
toView (there p) with toView p
... | MkView pref inf suff = MkView (_ ∷ pref) inf suff

fromView : ∀ {as bs} → View R as bs → Infix R as bs
fromView (MkView []         inf suff) = here (Prefix.fromView (inf Prefix.++ suff))
fromView (MkView (a ∷ pref) inf suff) = there (fromView (MkView pref inf suff))
