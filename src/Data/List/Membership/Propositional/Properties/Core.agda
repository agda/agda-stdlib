------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties related to propositional list membership.
------------------------------------------------------------------------

-- This file is needed to break the cyclic dependency with the proof
-- `Any-cong` in `Data.List.Relation.Unary.Any.Properties` which relies
-- on `Any↔` defined in this file.

{-# OPTIONS --without-K --safe #-}

module Data.List.Membership.Propositional.Properties.Core where

open import Data.List.Base using (List; [])
open import Data.List.Membership.Propositional using (_∈_; _∉_; find; lose)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Product.Base as Product using (_,_; ∃; _×_)
open import Function.Base using (flip; id; _∘_)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; trans; cong; resp)
open import Relation.Unary using (Pred; _⊆_)

private
  variable
    a p q : Level
    A : Set a
    x : A
    xs : List A

------------------------------------------------------------------------
-- Basics

∉[] : x ∉ []
∉[] ()

------------------------------------------------------------------------
-- find satisfies a simple equality when the predicate is a
-- propositional equality.

find-∈ : (x∈xs : x ∈ xs) → find x∈xs ≡ (x , x∈xs , refl)
find-∈ (here refl)  = refl
find-∈ (there x∈xs)
  = cong (λ where (x , x∈xs , eq) → x , there x∈xs , eq) (find-∈ x∈xs)

------------------------------------------------------------------------
-- Lemmas relating map and find.

module _ {P : Pred A p} where

  map∘find : (p : Any P xs) → let x , x∈xs , px = find p in
             {f : (x ≡_) ⊆ P} → f refl ≡ px →
             Any.map f x∈xs ≡ p
  map∘find (here  p) hyp = cong here  hyp
  map∘find (there p) hyp = cong there (map∘find p hyp)

  find∘map : ∀ {Q : Pred A q} {xs} (p : Any P xs) (f : P ⊆ Q) →
             let x , x∈xs , px = find p in
             find (Any.map f p) ≡ (x , x∈xs , f px)
  find∘map (here  p) f = refl
  find∘map (there p) f
    = cong (λ where (x , x∈xs , eq) → x , there x∈xs , eq) (find∘map p f)

------------------------------------------------------------------------
-- Any can be expressed using _∈_

module _ {P : Pred A p} where

  ∃∈-Any : (∃ λ x → x ∈ xs × P x) → Any P xs
  ∃∈-Any (x , x∈xs , px) = lose x∈xs px

  ∃∈-Any∘find : (p : Any P xs) → ∃∈-Any (find p) ≡ p
  ∃∈-Any∘find p = map∘find p refl

  find∘∃∈-Any : (p : ∃ λ x → x ∈ xs × P x) → find (∃∈-Any p) ≡ p
  find∘∃∈-Any p@(x , x∈xs , px)
    = trans (find∘map x∈xs (flip (resp P) px))
            (cong (λ (x , x∈xs , eq) → x , x∈xs , resp P eq px) (find-∈ x∈xs))

  Any↔ : (∃ λ x → x ∈ xs × P x) ↔ Any P xs
  Any↔ = mk↔ₛ′ ∃∈-Any find ∃∈-Any∘find find∘∃∈-Any

------------------------------------------------------------------------
-- Hence, find and lose are inverses (more or less).

lose∘find : ∀ {P : Pred A p} {xs} (p : Any P xs) → ∃∈-Any (find p) ≡ p
lose∘find = ∃∈-Any∘find

find∘lose : ∀ (P : Pred A p) {x xs}
            (x∈xs : x ∈ xs) (px : P x) →
            find (lose {P = P} x∈xs px) ≡ (x , x∈xs , px)
find∘lose P {x} x∈xs px = find∘∃∈-Any (x , x∈xs , px)
