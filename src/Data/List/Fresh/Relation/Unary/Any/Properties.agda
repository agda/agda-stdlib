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
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Data.List.Fresh
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
-- NonEmpty

module _ {x} {R : Rel A r} (R? : B.Decidable R) (¬R⇒S : ∀ {y} → ¬ R x y → S x y) where

  ¬Any⇒fresh : {xs : List# A R} → ¬ (Any (S x) xs) → x # xs
  ¬Any⇒fresh {[]}      ¬S = _
  ¬Any⇒fresh {a ∷# as} ¬S with R? x a
  ... | yes pr = pr , ¬Any⇒fresh (¬S ∘′ there)
  ... | no ¬pr = ⊥-elim (¬S (here (¬R⇒S ¬pr)))

module _ {x} {R : Rel A r} (R⇒¬S : ∀ {y} → R x y → ¬ (S x y)) where

  fresh⇒¬Any : {xs : List# A R} → x # xs → ¬ (Any (S x) xs)
  fresh⇒¬Any {a ∷# as} (p , ps) (here s)  = ⊥-elim (R⇒¬S p s)
  fresh⇒¬Any {a ∷# as} (p , ps) (there q) = fresh⇒¬Any ps q

------------------------------------------------------------------------
-- remove

length-remove : {xs : List# A R} (k : Any P xs) →
  length xs ≡ suc (length (xs ─ k))
length-remove (here _)  = refl
length-remove (there p) = cong suc (length-remove p)
