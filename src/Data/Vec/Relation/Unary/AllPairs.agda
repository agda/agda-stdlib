------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where every pair of elements are related (symmetrically)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Data.Vec.Relation.Unary.AllPairs
       {a ℓ} {A : Set a} {R : Rel A ℓ} where

open import Data.Nat.Base using (suc)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product as Prod using (_,_; _×_; uncurry; <_,_>)
open import Function using (id; _∘_)
open import Level using (_⊔_)
open import Relation.Binary as B using (Rel; _⇒_)
open import Relation.Binary.Construct.Intersection renaming (_∩_ to _∩ᵇ_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary as U renaming (_∩_ to _∩ᵘ_) hiding (_⇒_)
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)

------------------------------------------------------------------------
-- Definition

open import Data.Vec.Relation.Unary.AllPairs.Core public

------------------------------------------------------------------------
-- Operations

head : ∀ {n} {xs : Vec A (suc n)} → AllPairs R xs → All (R (Vec.head xs)) (Vec.tail xs)
head (px ∷ pxs) = px

tail : ∀ {n} {xs : Vec A (suc n)} → AllPairs R xs → AllPairs R (Vec.tail xs)
tail (px ∷ pxs) = pxs

uncons : ∀ {n} {xs : Vec A (suc n)} → AllPairs R xs →
         All (R (Vec.head xs)) (Vec.tail xs) × AllPairs R (Vec.tail xs)
uncons = < head , tail >

module _ {s} {S : Rel A s} where

  map : ∀ {n} → R ⇒ S → AllPairs R {n} ⊆ AllPairs S {n}
  map ~₁⇒~₂ [] = []
  map ~₁⇒~₂ (x~xs ∷ pxs) = All.map ~₁⇒~₂ x~xs ∷ (map ~₁⇒~₂ pxs)

module _ {s t} {S : Rel A s} {T : Rel A t} where

  zipWith : ∀ {n} → R ∩ᵇ S ⇒ T → AllPairs R {n} ∩ᵘ AllPairs S {n} ⊆ AllPairs T {n}
  zipWith f ([] , [])             = []
  zipWith f (px ∷ pxs , qx ∷ qxs) = All.map f (All.zip (px , qx)) ∷ zipWith f (pxs , qxs)

  unzipWith : ∀ {n} → T ⇒ R ∩ᵇ S → AllPairs T {n} ⊆ AllPairs R {n} ∩ᵘ AllPairs S {n}
  unzipWith f []         = [] , []
  unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (All.unzip (All.map f rx)) (unzipWith f rxs)

module _ {s} {S : Rel A s} where

  zip : ∀ {n} → AllPairs R {n} ∩ᵘ AllPairs S {n} ⊆ AllPairs (R ∩ᵇ S) {n}
  zip = zipWith id

  unzip : ∀ {n} → AllPairs (R ∩ᵇ S) {n} ⊆ AllPairs R {n} ∩ᵘ AllPairs S {n}
  unzip = unzipWith id

------------------------------------------------------------------------
-- Properties of predicates preserved by AllPairs

allPairs? : ∀ {n} → B.Decidable R → U.Decidable (AllPairs R {n})
allPairs? R? []       = yes []
allPairs? R? (x ∷ xs) =
  Dec.map′ (uncurry _∷_) uncons (All.all? (R? x) xs ×-dec allPairs? R? xs)

irrelevant : ∀ {n} → B.Irrelevant R → U.Irrelevant (AllPairs R {n})
irrelevant irr []           []           = refl
irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
  cong₂ _∷_ (All.irrelevant irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

satisfiable : U.Satisfiable (AllPairs R)
satisfiable = [] , []
