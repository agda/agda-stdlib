------------------------------------------------------------------------
-- The Agda standard library
--
-- All predicate transformer for fresh lists
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Fresh.Relation.Unary.All where

open import Level using (Level; _⊔_; Lift)
open import Data.Product using (_×_; _,_; proj₁; uncurry)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)

open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_)
open import Data.List.Fresh.Relation.Unary.Any as Any using (Any; here; there)

private
  variable
    a b p q r : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred A q
    R : Rel A r

module _ {A : Set a} {R : Rel A r} (P : Pred A p) where

  data All : List# A R → Set (p ⊔ a ⊔ r) where
    []  : All []
    _∷_ : ∀ {x xs pr} → P x → All xs → All (cons x xs pr)

uncons : ∀ {x} {xs : List# A R} {pr} → All P (cons x xs pr) → P x × All P xs
uncons (p ∷ ps) = p , ps

map : {xs : List# A R} → ∀[ P ⇒ Q ] → All P xs → All Q xs
map p⇒q []       = []
map p⇒q (p ∷ ps) = p⇒q p ∷ map p⇒q ps

lookup : {xs : List# A R} (ps : Any P xs) → All Q xs → Q (proj₁ (Any.witness ps))
lookup (here _)   (q ∷ _)  = q
lookup (there ps) (_ ∷ qs) = lookup ps qs

module _ {P : Pred A p} (P? : Decidable P) where

  all? : (xs : List# A R) → Dec (All P xs)
  all? []        = yes []
  all? (x ∷# xs) = Dec.map′ (uncurry _∷_) uncons (P? x ×-dec all? xs)
