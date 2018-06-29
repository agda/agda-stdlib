------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where all elements satisfy a given property
------------------------------------------------------------------------

module Data.List.All where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Any as Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product as Prod using (_,_)
open import Function
open import Level
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary hiding (_∈_)
open import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------
-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a p} {A : Set a}
         (P : A → Set p) : List A → Set (p ⊔ a) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on All

head : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
       All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : ∀ {a p} {A : Set a} {P : A → Set p} {x xs} →
       All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

lookup : ∀ {a p} {A : Set a} {P : A → Set p} {xs : List A} →
         All P xs → (∀ {x} → x ∈ xs → P x)
lookup []         ()
lookup (px ∷ pxs) (here refl)  = px
lookup (px ∷ pxs) (there x∈xs) = lookup pxs x∈xs

tabulate : ∀ {a p} {A : Set a} {P : A → Set p} {xs} →
           (∀ {x} → x ∈ xs → P x) → All P xs
tabulate {xs = []}     hyp = []
tabulate {xs = x ∷ xs} hyp = hyp (here refl) ∷ tabulate (hyp ∘ there)

map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} →
      P ⊆ Q → All P ⊆ All Q
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

zip : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} →
      All P ∩ All Q ⊆ All (P ∩ Q)
zip ([] , [])             = []
zip (px ∷ pxs , qx ∷ qxs) = (px , qx) ∷ zip (pxs , qxs)

unzip : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} →
        All (P ∩ Q) ⊆ All P ∩ All Q
unzip []           = [] , []
unzip (pqx ∷ pqxs) = Prod.zip _∷_ _∷_ pqx (unzip pqxs)

------------------------------------------------------------------------
-- Properties of predicates preserved by All

module _ {a p} {A : Set a} {P : A → Set p} where

  all : Decidable P → Decidable (All P)
  all p []       = yes []
  all p (x ∷ xs) with p x
  ... | yes px = Dec.map′ (px ∷_) tail (all p xs)
  ... | no ¬px = no (¬px ∘ head)

  universal : Universal P → Universal (All P)
  universal u []       = []
  universal u (x ∷ xs) = u x ∷ universal u xs

  irrelevant : Irrelevant P → Irrelevant (All P)
  irrelevant irr []           []           = P.refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    P.cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

  satisfiable : Satisfiable (All P)
  satisfiable = [] , []
