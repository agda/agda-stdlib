------------------------------------------------------------------------
-- The Agda standard library
--
-- Maybes where one of the elements satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Data.Maybe.Any where

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product as Prod using (∃; _,_; -,_)
open import Function using (id)
open import Function.Equivalence using (_⇔_; equivalence)
open import Level
open import Relation.Binary.PropositionalEquality as P using (_≡_; cong)
open import Relation.Unary
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

data Any {a p} {A : Set a} (P : Pred A p) : Pred (Maybe A) (a ⊔ p) where
  just : ∀ {x} → P x → Any P (just x)

------------------------------------------------------------------------
-- Basic operations

module _ {a p} {A : Set a} {P : Pred A p} where

  drop-just : ∀ {x} → Any P (just x) → P x
  drop-just (just px) = px

  just-equivalence : ∀ {x} → P x ⇔ Any P (just x)
  just-equivalence = equivalence just drop-just

  map : ∀ {q} {Q : Pred A q} → P ⊆ Q → Any P ⊆ Any Q
  map f (just px) = just (f px)

  satisfied : ∀ {x} → Any P x → ∃ P
  satisfied (just p) = -, p

------------------------------------------------------------------------
-- (un/)zip(/With)

module _ {a p q r} {A : Set a} {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

  zipWith : P ∩ Q ⊆ R → Any P ∩ Any Q ⊆ Any R
  zipWith f (just px , just qx) = just (f (px , qx))

  unzipWith : P ⊆ Q ∩ R → Any P ⊆ Any Q ∩ Any R
  unzipWith f (just px) = Prod.map just just (f px)

module _ {a p q} {A : Set a} {P : Pred A p} {Q : Pred A q} where

  zip : Any P ∩ Any Q ⊆ Any (P ∩ Q)
  zip = zipWith id

  unzip : Any (P ∩ Q) ⊆ Any P ∩ Any Q
  unzip = unzipWith id

------------------------------------------------------------------------
-- Seeing Any as a predicate transformer

module _ {a p} {A : Set a} {P : Pred A p} where

  dec : Decidable P → Decidable (Any P)
  dec P-dec nothing  = no λ ()
  dec P-dec (just x) = Dec.map just-equivalence (P-dec x)

  irrelevant : Irrelevant P → Irrelevant (Any P)
  irrelevant P-irrelevant (just p) (just q) = cong just (P-irrelevant p q)

  satisfiable : Satisfiable P → Satisfiable (Any P)
  satisfiable P-satisfiable = Prod.map just just P-satisfiable
