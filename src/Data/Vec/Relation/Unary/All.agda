------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Unary.All where

open import Data.Nat using (zero; suc)
open import Data.Fin using (Fin; zero; suc)
open import Data.Product as Prod using (_,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function using (_∘_)
open import Level using (_⊔_)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Unary
open import Relation.Binary.PropositionalEquality as P using (subst)

------------------------------------------------------------------------
-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a p} {A : Set a}
         (P : A → Set p) : ∀ {k} → Vec A k → Set (p ⊔ a) where
  []  : All P []
  _∷_ : ∀ {k x} {xs : Vec A k} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on All

head : ∀ {a p} {A : Set a} {P : A → Set p} {k x} {xs : Vec A k} →
       All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : ∀ {a p} {A : Set a} {P : A → Set p} {k x} {xs : Vec A k} →
       All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

lookup : ∀ {a p} {A : Set a} {P : A → Set p} {k} {xs : Vec A k} →
         (i : Fin k) → All P xs → P (Vec.lookup xs i)
lookup zero    (px ∷ pxs) = px
lookup (suc i) (px ∷ pxs) = lookup i pxs

tabulate : ∀ {a p} {A : Set a} {P : A → Set p} {k xs} →
           (∀ i → P (Vec.lookup xs i)) → All P {k} xs
tabulate {xs = []}    pxs = []
tabulate {xs = _ ∷ _} pxs = pxs zero ∷ tabulate (pxs ∘ suc)

map : ∀ {a p q} {A : Set a} {P : A → Set p} {Q : A → Set q} {k} →
      P ⊆ Q → All P {k} ⊆ All Q {k}
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

zipWith : ∀ {a b c p q r} {A : Set a} {B : Set b} {C : Set c} {_⊕_ : A → B → C}
          {P : A → Set p} {Q : B → Set q} {R : C → Set r} →
          (∀ {x y} → P x → Q y → R (x ⊕ y)) →
          ∀ {k xs ys} → All P {k} xs → All Q {k} ys →
          All R {k} (Vec.zipWith _⊕_ xs ys)
zipWith _⊕_ {xs = []}     {[]}     []         []         = []
zipWith _⊕_ {xs = x ∷ xs} {y ∷ ys} (px ∷ pxs) (qy ∷ qys) =
  px ⊕ qy ∷ zipWith _⊕_ pxs qys

zip : ∀ {a p q k} {A : Set a} {P : A → Set p} {Q : A → Set q} →
      All P ∩ All Q ⊆ All (P ∩ Q) {k}
zip ([] , [])             = []
zip (px ∷ pxs , qx ∷ qxs) = (px , qx) ∷ zip (pxs , qxs)

unzip : ∀ {a p q k} {A : Set a} {P : A → Set p} {Q : A → Set q} →
        All (P ∩ Q) {k} ⊆ All P ∩ All Q
unzip []           = [] , []
unzip (pqx ∷ pqxs) = Prod.zip _∷_ _∷_ pqx (unzip pqxs)

------------------------------------------------------------------------
-- Properties of predicates preserved by All

module _ {a p} {A : Set a} {P : A → Set p} where

  all : ∀ {k} → Decidable P → Decidable (All P {k})
  all P? []       = yes []
  all P? (x ∷ xs) with P? x
  ... | yes px = Dec.map′ (px ∷_) tail (all P? xs)
  ... | no ¬px = no (¬px ∘ head)

  universal : Universal P → ∀ {k} → Universal (All P {k})
  universal u []       = []
  universal u (x ∷ xs) = u x ∷ universal u xs

  irrelevant : Irrelevant P → ∀ {k} → Irrelevant (All P {k})
  irrelevant irr []           []           = P.refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    P.cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

  satisfiable : Satisfiable P → ∀ {k} → Satisfiable (All P {k})
  satisfiable (x , p) {zero}  = [] , []
  satisfiable (x , p) {suc k} = Prod.map (x ∷_) (p ∷_) (satisfiable (x , p))
