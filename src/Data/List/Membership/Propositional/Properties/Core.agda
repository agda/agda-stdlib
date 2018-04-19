------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties related to propositional list membership.
--
-- This file is needed to break the cyclic dependency with the proof
-- `Any-cong` in `Data.Any.Properties` which relies on `Any↔` in this
-- file.
------------------------------------------------------------------------

module Data.List.Membership.Propositional.Properties.Core where

open import Function using (flip; id; _∘_)
open import Function.Inverse as Inv using (_↔_)
open import Data.List.Base using (List)
open import Data.List.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional
open import Data.Product as Prod
  using (_,_; proj₁; proj₂; uncurry′; ∃; _×_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; _≗_)
open import Relation.Unary using (_⊆_)

-- Lemmas relating map and find.

map∘find : ∀ {a p} {A : Set a} {P : A → Set p} {xs}
           (p : Any P xs) → let p′ = find p in
           {f : _≡_ (proj₁ p′) ⊆ P} →
           f refl ≡ proj₂ (proj₂ p′) →
           Any.map f (proj₁ (proj₂ p′)) ≡ p
map∘find (here  p) hyp = P.cong here  hyp
map∘find (there p) hyp = P.cong there (map∘find p hyp)

find∘map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q}
           {xs : List A} (p : Any P xs) (f : P ⊆ Q) →
           find (Any.map f p) ≡ Prod.map id (Prod.map id f) (find p)
find∘map (here  p) f = refl
find∘map (there p) f rewrite find∘map p f = refl

-- find satisfies a simple equality when the predicate is a
-- propositional equality.

find-∈ : ∀ {a} {A : Set a} {x : A} {xs : List A} (x∈xs : x ∈ xs) →
         find x∈xs ≡ (x , x∈xs , refl)
find-∈ (here refl)  = refl
find-∈ (there x∈xs) rewrite find-∈ x∈xs = refl

-- find and lose are inverses (more or less).

lose∘find : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A}
            (p : Any P xs) →
            uncurry′ lose (proj₂ (find p)) ≡ p
lose∘find p = map∘find p P.refl

find∘lose : ∀ {a p} {A : Set a} (P : A → Set p) {x xs}
            (x∈xs : x ∈ xs) (pp : P x) →
            find {P = P} (lose x∈xs pp) ≡ (x , x∈xs , pp)
find∘lose P x∈xs p
  rewrite find∘map x∈xs (flip (P.subst P) p)
        | find-∈ x∈xs
        = refl

-- Any can be expressed using _∈_

∃∈-Any : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
         (∃ λ x → x ∈ xs × P x) → Any P xs
∃∈-Any = uncurry′ lose ∘ proj₂

Any↔ : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
       (∃ λ x → x ∈ xs × P x) ↔ Any P xs
Any↔ {P = P} {xs} = record
  { to         = P.→-to-⟶ ∃∈-Any
  ; from       = P.→-to-⟶ find
  ; inverse-of = record
    { left-inverse-of  = λ p →
        find∘lose P (proj₁ (proj₂ p)) (proj₂ (proj₂ p))
    ; right-inverse-of = lose∘find
    }
  }
