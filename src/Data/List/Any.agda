------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where at least one element satisfies a given property
------------------------------------------------------------------------

module Data.List.Any {a} {A : Set a} where

open import Data.Empty
open import Data.Fin
open import Data.List.Base as List using (List; []; [_]; _∷_)
open import Data.Product as Prod using (∃; _,_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Level using (_⊔_)
open import Relation.Nullary using (¬_; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Unary hiding (_∈_)

------------------------------------------------------------------------
-- Any P xs means that at least one element in xs satisfies P.

data Any {p} (P : A → Set p) : List A → Set (a ⊔ p) where
  here  : ∀ {x xs} (px  : P x)      → Any P (x ∷ xs)
  there : ∀ {x xs} (pxs : Any P xs) → Any P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on Any

module _ {p} {P : A → Set p} {x xs} where

  head : ¬ Any P xs → Any P (x ∷ xs) → P x
  head ¬pxs (here px)   = px
  head ¬pxs (there pxs) = contradiction pxs ¬pxs

  tail : ¬ P x → Any P (x ∷ xs) → Any P xs
  tail ¬px (here  px)  = ⊥-elim (¬px px)
  tail ¬px (there pxs) = pxs

map : ∀ {p q} {P : A → Set p} {Q : A → Set q} → P ⊆ Q → Any P ⊆ Any Q
map g (here px)   = here (g px)
map g (there pxs) = there (map g pxs)

-- `index x∈xs` is the list position (zero-based) which `x∈xs` points to.
index : ∀ {p} {P : A → Set p} {xs} → Any P xs → Fin (List.length xs)
index (here  px)  = zero
index (there pxs) = suc (index pxs)

-- If any element satisfies P, then P is satisfied.
satisfied : ∀ {p} {P : A → Set p} {xs} → Any P xs → ∃ P
satisfied (here px) = _ , px
satisfied (there pxs) = satisfied pxs

module _ {p} {P : A → Set p} {x xs} where

  toSum : Any P (x ∷ xs) → P x ⊎ Any P xs
  toSum (here px)   = inj₁ px
  toSum (there pxs) = inj₂ pxs

  fromSum : P x ⊎ Any P xs → Any P (x ∷ xs)
  fromSum (inj₁ px)  = here px
  fromSum (inj₂ pxs) = there pxs

------------------------------------------------------------------------
-- Properties of predicates preserved by Any

module _ {p} {P : A → Set p} where

  any : Decidable P → Decidable (Any P)
  any P? []       = no λ()
  any P? (x ∷ xs) with P? x
  ... | yes px = yes (here px)
  ... | no ¬px = Dec.map′ there (tail ¬px) (any P? xs)

  satisfiable : Satisfiable P → Satisfiable (Any P)
  satisfiable (x , Px) = [ x ] , here Px
