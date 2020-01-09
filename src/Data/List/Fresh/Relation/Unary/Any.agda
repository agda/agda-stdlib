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
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)

open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_)

private
  variable
    a p q r : Level
    A : Set a

module _ {A : Set a} {R : Rel A r} (P : Pred A p) where

  data Any : List# A R → Set (p ⊔ a ⊔ r) where
    here  : ∀ {x xs pr} → P x → Any (cons x xs pr)
    there : ∀ {x xs pr} → Any xs → Any (cons x xs pr)

module _ {R : Rel A r} {P : Pred A p} {x} {xs : List# A R} {pr} where

  head : ¬ Any P xs → Any P (cons x xs pr) → P x
  head ¬tail (here p)   = p
  head ¬tail (there ps) = ⊥-elim (¬tail ps)

  tail : ¬ P x → Any P (cons x xs pr) → Any P xs
  tail ¬head (here p)   = ⊥-elim (¬head p)
  tail ¬head (there ps) = ps

  toSum : Any P (cons x xs pr) → P x ⊎ Any P xs
  toSum (here p) = inj₁ p
  toSum (there ps) = inj₂ ps

  fromSum : P x ⊎ Any P xs → Any P (cons x xs pr)
  fromSum = [ here , there ]′

  ⊎⇔Any : (P x ⊎ Any P xs) ⇔ Any P (cons x xs pr)
  ⊎⇔Any = equivalence fromSum toSum

module _ {R : Rel A r} {P : Pred A p} {Q : Pred A q} where

  map : {xs : List# A R} → ∀[ P ⇒ Q ] → Any P xs → Any Q xs
  map p⇒q (here p)  = here (p⇒q p)
  map p⇒q (there p) = there (map p⇒q p)

module _ {R : Rel A r} {P : Pred A p} where

  witness : {xs : List# A R} → Any P xs → ∃ P
  witness (here p)   = -, p
  witness (there ps) = witness ps

  remove   : (xs : List# A R) → Any P xs → List# A R
  remove-# : ∀ {x} {xs : List# A R} p → x # xs → x # (remove xs p)

  remove (_ ∷# xs)      (here _)  = xs
  remove (cons x xs pr) (there k) = cons x (remove xs k) (remove-# k pr)

  remove-# (here x)  (p , ps) = ps
  remove-# (there k) (p , ps) = p , remove-# k ps

infixl 4 _─_
_─_ = remove

module _ {R : Rel A r} {P : Pred A p} (P? : Decidable P) where

  any? : (xs : List# A R) → Dec (Any P xs)
  any? []        = no (λ ())
  any? (x ∷# xs) = Dec.map ⊎⇔Any (P? x ⊎-dec any? xs)
