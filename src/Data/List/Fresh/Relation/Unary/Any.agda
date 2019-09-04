------------------------------------------------------------------------
-- The Agda standard library
--
-- Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.Any where

open import Level using (Level; _⊔_; Lift)
open import Data.Product using (_,_)
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)

open import Data.List.Fresh

private
  variable
    a b p q r : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    R : Rel A r

module _ {A : Set a} {R : Rel A r} (P : Pred A p) where

  data Any : List# A R → Set (p ⊔ a ⊔ r) where
    here  : ∀ {x xs pr} → P x → Any (cons x xs pr)
    there : ∀ {x xs pr} → Any xs → Any (cons x xs pr)

map : {xs : List# A R} → ∀[ P ⇒ Q ] → Any P xs → Any Q xs
map p⇒q (here p)  = here (p⇒q p)
map p⇒q (there p) = there (map p⇒q p)

remove   : (xs : List# A R) → Any P xs → List# A R
remove-# : ∀ {x} {xs : List# A R} (p : Any P xs) → x # xs → x # (remove xs p)

remove (_ ∷# xs)      (here _)  = xs
remove (cons x xs pr) (there k) = cons x (remove xs k) (remove-# k pr)

remove-# (here x)  (p , ps) = ps
remove-# (there k) (p , ps) = p , remove-# k ps

infixl 4 _─_
_─_ = remove
