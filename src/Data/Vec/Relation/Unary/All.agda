------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Unary.All where

open import Data.Nat.Base using (zero; suc)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product as Prod using (_×_; _,_; uncurry; <_,_>)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Function using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Nullary hiding (Irrelevant)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary
open import Relation.Binary.PropositionalEquality as P using (subst)

private
  variable
    a b c p q r : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {a} {A : Set a} (P : Pred A p) : ∀ {n} → Vec A n → Set (p ⊔ a) where
  []  : All P []
  _∷_ : ∀ {n x} {xs : Vec A n} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on All

module _ {P : Pred A p} where

  head : ∀ {n x} {xs : Vec A n} → All P (x ∷ xs) → P x
  head (px ∷ pxs) = px

  tail : ∀ {n x} {xs : Vec A n} → All P (x ∷ xs) → All P xs
  tail (px ∷ pxs) = pxs

  uncons : ∀ {n x} {xs : Vec A n} → All P (x ∷ xs) → P x × All P xs
  uncons = < head , tail >

  lookup : ∀ {n} {xs : Vec A n} (i : Fin n) →
           All P xs → P (Vec.lookup xs i)
  lookup zero    (px ∷ pxs) = px
  lookup (suc i) (px ∷ pxs) = lookup i pxs

  tabulate : ∀ {n xs} → (∀ i → P (Vec.lookup xs i)) → All P {n} xs
  tabulate {xs = []}    pxs = []
  tabulate {xs = _ ∷ _} pxs = pxs zero ∷ tabulate (pxs ∘ suc)

module _ {P : Pred A p} {Q : Pred A q} where

  map : ∀ {n} → P ⊆ Q → All P {n} ⊆ All Q {n}
  map g []         = []
  map g (px ∷ pxs) = g px ∷ map g pxs

  zip : ∀ {n} → All P ∩ All Q ⊆ All (P ∩ Q) {n}
  zip ([] , [])             = []
  zip (px ∷ pxs , qx ∷ qxs) = (px , qx) ∷ zip (pxs , qxs)

  unzip : ∀ {n} → All (P ∩ Q) {n} ⊆ All P ∩ All Q
  unzip []           = [] , []
  unzip (pqx ∷ pqxs) = Prod.zip _∷_ _∷_ pqx (unzip pqxs)

module _ {P : Pred A p} {Q : Pred B q} {R : Pred C r} where

  zipWith : ∀ {_⊕_ : A → B → C} →
            (∀ {x y} → P x → Q y → R (x ⊕ y)) →
            ∀ {n xs ys} → All P {n} xs → All Q {n} ys →
            All R {n} (Vec.zipWith _⊕_ xs ys)
  zipWith _⊕_ {xs = []}     {[]}     []         []         = []
  zipWith _⊕_ {xs = x ∷ xs} {y ∷ ys} (px ∷ pxs) (qy ∷ qys) =
    px ⊕ qy ∷ zipWith _⊕_ pxs qys

------------------------------------------------------------------------
-- Properties of predicates preserved by All

module _ {P : Pred A p} where

  all : ∀ {n} → Decidable P → Decidable (All P {n})
  all P? []       = yes []
  all P? (x ∷ xs) = Dec.map′ (uncurry _∷_) uncons (P? x ×-dec all P? xs)

  universal : Universal P → ∀ {n} → Universal (All P {n})
  universal u []       = []
  universal u (x ∷ xs) = u x ∷ universal u xs

  irrelevant : Irrelevant P → ∀ {n} → Irrelevant (All P {n})
  irrelevant irr []           []           = P.refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    P.cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

  satisfiable : Satisfiable P → ∀ {n} → Satisfiable (All P {n})
  satisfiable (x , p) {zero}  = [] , []
  satisfiable (x , p) {suc n} = Prod.map (x ∷_) (p ∷_) (satisfiable (x , p))
