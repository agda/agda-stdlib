------------------------------------------------------------------------
-- The Agda standard library
--
-- An inductive definition of the heterogeneous prefix relation
------------------------------------------------------------------------

module Data.List.Relation.Prefix.Heterogeneous where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Pointwise using (Pointwise; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary using (REL; _⇒_)

data Prefix {a b r} {A : Set a} {B : Set b} (R : REL A B r)
          : REL (List A) (List B) r where
  []  : ∀ {bs} → Prefix R [] bs
  _∷_ : ∀ {a b as bs} → R a b → Prefix R as bs → Prefix R (a ∷ as) (b ∷ bs)


module _ {a b r} {A : Set a} {B : Set b} {R : REL A B r} where

  uncons : ∀ {a b as bs} → Prefix R (a ∷ as) (b ∷ bs) → R a b × Prefix R as bs
  uncons (x ∷ xs) = x , xs

module _ {a b r s} {A : Set a} {B : Set b} {R : REL A B r} {S : REL A B s} where

  map : R ⇒ S → Prefix R ⇒ Prefix S
  map f []       = []
  map f (x ∷ xs) = f x ∷ map f xs

