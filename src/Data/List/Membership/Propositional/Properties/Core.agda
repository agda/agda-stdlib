------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties related to propositional list membership.
------------------------------------------------------------------------

-- This file is needed to break the cyclic dependency with the proof
-- `Any-cong` in `Data.List.Relation.Unary.Any.Properties` which relies
-- on `Any↔` defined in this file.

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Membership.Propositional.Properties.Core where

open import Function.Base using (flip; id; _∘_)
open import Function.Bundles
open import Data.List.Base using (List)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional
open import Data.Product.Base as Product
  using (_,_; proj₁; proj₂; uncurry′; ∃; _×_)
open import Level using (Level)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; subst)
open import Relation.Unary using (Pred; _⊆_)

private
  variable
    a p q : Level
    A : Set a

------------------------------------------------------------------------
-- Lemmas relating map and find.

map∘find : ∀ {P : Pred A p} {xs}
           (p : Any P xs) → let p′ = find p in
           {f : _≡_ (proj₁ p′) ⊆ P} →
           f refl ≡ proj₂ (proj₂ p′) →
           Any.map f (proj₁ (proj₂ p′)) ≡ p
map∘find (here  p) hyp = cong here  hyp
map∘find (there p) hyp = cong there (map∘find p hyp)

find∘map : ∀ {P : Pred A p} {Q : Pred A q}
           {xs : List A} (p : Any P xs) (f : P ⊆ Q) →
           find (Any.map f p) ≡ Product.map id (Product.map id f) (find p)
find∘map (here  p) f = refl
find∘map (there p) f rewrite find∘map p f = refl

------------------------------------------------------------------------
-- find satisfies a simple equality when the predicate is a
-- propositional equality.

find-∈ : ∀ {x : A} {xs : List A} (x∈xs : x ∈ xs) →
         find x∈xs ≡ (x , x∈xs , refl)
find-∈ (here refl)  = refl
find-∈ (there x∈xs) rewrite find-∈ x∈xs = refl

------------------------------------------------------------------------
-- find and lose are inverses (more or less).

lose∘find : ∀ {P : Pred A p} {xs : List A}
            (p : Any P xs) →
            uncurry′ lose (proj₂ (find p)) ≡ p
lose∘find p = map∘find p refl

find∘lose : ∀ (P : Pred A p) {x xs}
            (x∈xs : x ∈ xs) (pp : P x) →
            find {P = P} (lose x∈xs pp) ≡ (x , x∈xs , pp)
find∘lose P x∈xs p
  rewrite find∘map x∈xs (flip (subst P) p)
        | find-∈ x∈xs
        = refl

------------------------------------------------------------------------
-- Any can be expressed using _∈_

module _ {P : Pred A p} where

  ∃∈-Any : ∀  {xs} → (∃ λ x → x ∈ xs × P x) → Any P xs
  ∃∈-Any = uncurry′ lose ∘ proj₂

  Any↔ : ∀ {xs} → (∃ λ x → x ∈ xs × P x) ↔ Any P xs
  Any↔ = mk↔ₛ′ ∃∈-Any find lose∘find from∘to
    where
    from∘to : ∀ v → find (∃∈-Any v) ≡ v
    from∘to p = find∘lose _ (proj₁ (proj₂ p)) (proj₂ (proj₂ p))
