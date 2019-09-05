------------------------------------------------------------------------
-- The Agda standard library
--
-- Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.Any where

open import Level using (Level; _⊔_; Lift)
open import Data.Empty
open import Data.Product using (∃; _,_; -,_)
open import Data.Sum.Base using (_⊎_; [_,_]′; inj₁; inj₂)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)

open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_)

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

module _ {x} {xs : List# A R} {pr} where

  head : ¬ Any P xs → Any P (cons x xs pr) → P x
  head ¬tail (here p)   = p
  head ¬tail (there ps) = ⊥-elim (¬tail ps)

  tail : ¬ P x → Any P (cons x xs pr) → Any P xs
  tail ¬head (here p)   = ⊥-elim (¬head p)
  tail ¬head (there ps) = ps

map : {xs : List# A R} → ∀[ P ⇒ Q ] → Any P xs → Any Q xs
map p⇒q (here p)  = here (p⇒q p)
map p⇒q (there p) = there (map p⇒q p)

witness : {xs : List# A R} → Any P xs → ∃ P
witness (here p)   = -, p
witness (there ps) = witness ps

remove   : (xs : List# A R) → Any P xs → List# A R
remove-# : ∀ {x} {xs : List# A R} (p : Any P xs) → x # xs → x # (remove xs p)

remove (_ ∷# xs)      (here _)  = xs
remove (cons x xs pr) (there k) = cons x (remove xs k) (remove-# k pr)

remove-# (here x)  (p , ps) = ps
remove-# (there k) (p , ps) = p , remove-# k ps

infixl 4 _─_
_─_ = remove

module _ {P : Pred A p} (P? : Decidable P) where

  any? : (xs : List# A R) → Dec (Any P xs)
  any? []        = no (λ ())
  any? (x ∷# xs) with P? x
  ... | yes p = yes (here p)
  ... | no ¬p = Dec.map′ there (tail ¬p) (any? xs)
