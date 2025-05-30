------------------------------------------------------------------------
-- The Agda standard library
--
-- Maybes where one of the elements satisfies a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Maybe.Relation.Unary.Any where

open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product.Base as Product using (∃; _,_; -,_)
open import Function.Base using (id)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong)
open import Relation.Unary
  using (Pred; _⊆_; _∩_; Decidable; Irrelevant; Satisfiable)
open import Relation.Nullary.Decidable as Dec using (Dec; yes; no)

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
  just-equivalence = mk⇔ just drop-just

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
  unzipWith f (just px) = Product.map just just (f px)

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
  satisfiable P-satisfiable = Product.map just just P-satisfiable
