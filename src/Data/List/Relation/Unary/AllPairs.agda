------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where every pair of elements are related (symmetrically)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Rel)

module Data.List.Relation.Unary.AllPairs
       {a ℓ} {A : Set a} {R : Rel A ℓ} where

open import Data.List.Base using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
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

open import Data.List.Relation.Unary.AllPairs.Core public

------------------------------------------------------------------------
-- Operations

head : ∀ {x xs} → AllPairs R (x ∷ xs) → All (R x) xs
head (px ∷ pxs) = px

tail : ∀ {x xs} → AllPairs R (x ∷ xs) → AllPairs R xs
tail (px ∷ pxs) = pxs

uncons : ∀ {x xs} → AllPairs R (x ∷ xs) → All (R x) xs × AllPairs R xs
uncons = < head , tail >

module _ {q} {S : Rel A q} where

  map : R ⇒ S → AllPairs R ⊆ AllPairs S
  map ~₁⇒~₂ [] = []
  map ~₁⇒~₂ (x~xs ∷ pxs) = All.map ~₁⇒~₂ x~xs ∷ (map ~₁⇒~₂ pxs)

module _ {s t} {S : Rel A s} {T : Rel A t} where

  zipWith : R ∩ᵇ S ⇒ T → AllPairs R ∩ᵘ AllPairs S ⊆ AllPairs T
  zipWith f ([] , [])             = []
  zipWith f (px ∷ pxs , qx ∷ qxs) = All.zipWith f (px , qx) ∷ zipWith f (pxs , qxs)

  unzipWith : T ⇒ R ∩ᵇ S → AllPairs T ⊆ AllPairs R ∩ᵘ AllPairs S
  unzipWith f []         = [] , []
  unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (All.unzipWith f rx) (unzipWith f rxs)

module _ {s} {S : Rel A s} where

  zip : AllPairs R ∩ᵘ AllPairs S ⊆ AllPairs (R ∩ᵇ S)
  zip = zipWith id

  unzip : AllPairs (R ∩ᵇ S) ⊆ AllPairs R ∩ᵘ AllPairs S
  unzip = unzipWith id

------------------------------------------------------------------------
-- Properties of predicates preserved by AllPairs

allPairs? : B.Decidable R → U.Decidable (AllPairs R)
allPairs? R? []       = yes []
allPairs? R? (x ∷ xs) =
  Dec.map′ (uncurry _∷_) uncons (All.all (R? x) xs ×-dec allPairs? R? xs)

irrelevant : B.Irrelevant R → U.Irrelevant (AllPairs R)
irrelevant irr []           []           = refl
irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
  cong₂ _∷_ (All.irrelevant irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

satisfiable : U.Satisfiable (AllPairs R)
satisfiable = [] , []
