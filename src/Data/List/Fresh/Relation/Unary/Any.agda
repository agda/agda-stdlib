------------------------------------------------------------------------
-- The Agda standard library
--
-- Any predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.List.Fresh.Relation.Unary.Any where

open import Level using (Level; _⊔_; Lift)
open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_; fresh)
open import Data.Product.Base using (∃; _,_; -,_)
open import Data.Sum.Base using (_⊎_; [_,_]′; inj₁; inj₂)
open import Function.Bundles using (_⇔_; mk⇔)
open import Level using (Level; _⊔_; Lift)
open import Relation.Nullary.Negation using (¬_; contradiction)
open import Relation.Nullary.Decidable as Dec using (Dec; no; _⊎?_)
open import Relation.Unary as Unary
  using (Pred; IUniversal; Universal; Decidable; _⇒_; _∪_; _∩_)
open import Relation.Binary.Core using (Rel)

private
  variable
    a p q r : Level
    A : Set a
    R : Rel A r
    P : Pred A p
    Q : Pred A q
    x : A
    xs : List# A R


module _ {A : Set a} {R : Rel A r} (P : Pred A p) where

  data Any : List# A R → Set (p ⊔ a ⊔ r) where
    here  : ∀ {x xs pr} → P x → Any (cons x xs pr)
    there : ∀ {x xs pr} → Any xs → Any (cons x xs pr)

module _ {pr : fresh A R x xs} where

  head : ¬ Any P xs → Any P (cons x xs pr) → P x
  head ¬tail (here p)   = p
  head ¬tail (there ps) = contradiction ps ¬tail

  tail : ¬ P x → Any P (cons x xs pr) → Any P xs
  tail ¬head (here p)   = contradiction p ¬head
  tail ¬head (there ps) = ps

  toSum : Any P (cons x xs pr) → P x ⊎ Any P xs
  toSum (here p) = inj₁ p
  toSum (there ps) = inj₂ ps

  fromSum : P x ⊎ Any P xs → Any P (cons x xs pr)
  fromSum = [ here , there ]′

  ⊎⇔Any : (P x ⊎ Any P xs) ⇔ Any P (cons x xs pr)
  ⊎⇔Any = mk⇔ fromSum toSum

map : ∀[ P ⇒ Q ] → Any P xs → Any Q xs
map p⇒q (here p)  = here (p⇒q p)
map p⇒q (there p) = there (map p⇒q p)

witness : Any P xs → ∃ P
witness (here p)   = -, p
witness (there ps) = witness ps

remove   : (xs : List# A R) → Any P xs → List# A R
remove-# : (p : Any {R = R} P xs) → x # xs → x # (remove xs p)

remove (_ ∷# xs)      (here _)  = xs
remove (cons x xs pr) (there k) = cons x (remove xs k) (remove-# k pr)

remove-# (here x)  (p , ps) = ps
remove-# (there k) (p , ps) = p , remove-# k ps

infixl 4 _─_
_─_ = remove

module _ (P? : Decidable P) where

  any? : ∀ xs → Dec (Any {R = R} P xs)
  any? []        = no λ()
  any? (x ∷# xs) = Dec.map ⊎⇔Any (P? x ⊎? any? xs)
