------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where every pair of elements are related (symmetrically)
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.AllPairs where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product as Prod using (_,_; _×_)
open import Function using (id; _∘_)
open import Level using (_⊔_)
open import Relation.Binary as B using (Rel; _⇒_)
open import Relation.Binary.Construct.Intersection renaming (_∩_ to _∩ᵇ_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary as U renaming (_∩_ to _∩ᵘ_) hiding (_⇒_)
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec

------------------------------------------------------------------------
-- Definition

-- AllPairs R xs means that every pair of elements (x , y) in xs is a
-- member of relation R (as long as x comes before y in the list).

infixr 5 _∷_

data AllPairs {a ℓ} {A : Set a} (R : Rel A ℓ) : List A → Set (a ⊔ ℓ) where
  []  : AllPairs R []
  _∷_ : ∀ {x xs} → All (R x) xs → AllPairs R xs → AllPairs R (x ∷ xs)

------------------------------------------------------------------------
-- Operations

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  head : ∀ {x xs} → AllPairs R (x ∷ xs) → All (R x) xs
  head (px ∷ pxs) = px

  tail : ∀ {x xs} → AllPairs R (x ∷ xs) → AllPairs R xs
  tail (px ∷ pxs) = pxs

module _ {a p q} {A : Set a} {R : Rel A p} {S : Rel A q} where

  map : R ⇒ S → AllPairs R ⊆ AllPairs S
  map ~₁⇒~₂ [] = []
  map ~₁⇒~₂ (x~xs ∷ pxs) = All.map ~₁⇒~₂ x~xs ∷ (map ~₁⇒~₂ pxs)

module _ {a p q r} {A : Set a} {P : Rel A p} {Q : Rel A q} {R : Rel A r} where

  zipWith : P ∩ᵇ Q ⇒ R → AllPairs P ∩ᵘ AllPairs Q ⊆ AllPairs R
  zipWith f ([] , [])             = []
  zipWith f (px ∷ pxs , qx ∷ qxs) = All.zipWith f (px , qx) ∷ zipWith f (pxs , qxs)

  unzipWith : R ⇒ P ∩ᵇ Q → AllPairs R ⊆ AllPairs P ∩ᵘ AllPairs Q
  unzipWith f []         = [] , []
  unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (All.unzipWith f rx) (unzipWith f rxs)

module _ {a p q} {A : Set a} {P : Rel A p} {Q : Rel A q} where

  zip : AllPairs P ∩ᵘ AllPairs Q ⊆ AllPairs (P ∩ᵇ Q)
  zip = zipWith id

  unzip : AllPairs (P ∩ᵇ Q) ⊆ AllPairs P ∩ᵘ AllPairs Q
  unzip = unzipWith id

------------------------------------------------------------------------
-- Properties of predicates preserved by AllPairs

module _ {a ℓ} {A : Set a} {R : Rel A ℓ} where

  allPairs? : B.Decidable R → U.Decidable (AllPairs R)
  allPairs? R? []       = yes []
  allPairs? R? (x ∷ xs) with All.all (R? x) xs
  ... | yes px = Dec.map′ (px ∷_) tail (allPairs? R? xs)
  ... | no ¬px = no (¬px ∘ head)

  irrelevant : B.Irrelevant R → U.Irrelevant (AllPairs R)
  irrelevant irr []           []           = refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    cong₂ _∷_ (All.irrelevant irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

  satisfiable : U.Satisfiable (AllPairs R)
  satisfiable = [] , []
