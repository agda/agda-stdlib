------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.Any.Properties where

open import Level using (Level; _⊔_; Lift)
open import Data.Empty
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Function using (_∘′_)
open import Relation.Nullary
open import Relation.Unary  as U using (Pred)
open import Relation.Binary as B using (Rel)
open import Relation.Nary
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.List.Fresh
open import Data.List.Fresh.Relation.Unary.All
open import Data.List.Fresh.Relation.Unary.Any

private
  variable
    a b p q r s : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    R : Rel A r
    S : Rel A s

------------------------------------------------------------------------
-- NonEmpty

Any⇒NonEmpty : {xs : List# A R} → Any P xs → NonEmpty xs
Any⇒NonEmpty {xs = cons x xs pr} p  = cons x xs pr

------------------------------------------------------------------------
-- Correspondence between Any and All

module _ {P : Pred A p} {Q : Pred A q} (P⇒¬Q : ∀[ P ⇒ ∁ Q ]) where

  Any⇒¬All : {xs : List# A R} → Any P xs → ¬ (All Q xs)
  Any⇒¬All (here p)   (q ∷ _)  = P⇒¬Q p q
  Any⇒¬All (there ps) (_ ∷ qs) = Any⇒¬All ps qs

  All⇒¬Any : {xs : List# A R} → All P xs → ¬ (Any Q xs)
  All⇒¬Any (p ∷ _)  (here q)   = P⇒¬Q p q
  All⇒¬Any (_ ∷ ps) (there qs) = All⇒¬Any ps qs

module _ {P : Pred A p} {Q : Pred A q} (P? : Decidable P) where

  ¬All⇒Any : {xs : List# A R} → ¬ (All P xs) → Any (∁ P) xs
  ¬All⇒Any {xs = []}      ¬ps = ⊥-elim (¬ps [])
  ¬All⇒Any {xs = x ∷# xs} ¬ps with P? x
  ... | yes p = there (¬All⇒Any (¬ps ∘′ (p ∷_)))
  ... | no ¬p = here ¬p

  ¬Any⇒All : {xs : List# A R} → ¬ (Any P xs) → All (∁ P) xs
  ¬Any⇒All {xs = []}      ¬ps = []
  ¬Any⇒All {xs = x ∷# xs} ¬ps with P? x
  ... | yes p = ⊥-elim (¬ps (here p))
  ... | no ¬p = ¬p ∷ ¬Any⇒All (¬ps ∘′ there)

------------------------------------------------------------------------
-- remove

length-remove : {xs : List# A R} (k : Any P xs) →
  length xs ≡ suc (length (xs ─ k))
length-remove (here _)  = refl
length-remove (there p) = cong suc (length-remove p)
