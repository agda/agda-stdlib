------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where every consecutative pair of elements is related.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.AllNeighbours {a} {A : Set a} where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product as Prod using (_,_; _×_)
open import Function using (id; _∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary as B using (Rel; _⇒_)
open import Relation.Binary.Construct.Intersection renaming (_∩_ to _∩ᵇ_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary as U renaming (_∩_ to _∩ᵘ_) hiding (_⇒_)
open import Relation.Nullary using (yes; no)
import Relation.Nullary.Decidable as Dec

private
  variable
    p q r ℓ : Level

------------------------------------------------------------------------
-- Definition

-- AllNeighbours R xs means that every consecutative pair of elements
-- in xs is a member of relation R.

infixr 5 _∷_

data AllNeighbours (R : Rel A ℓ) : List A → Set (a ⊔ ℓ) where
  []  : AllNeighbours R []
  [-] : ∀ {x} → AllNeighbours R (x ∷ [])
  _∷_ : ∀ {x y xs} → R x y → AllNeighbours R (y ∷ xs) → AllNeighbours R (x ∷ y ∷ xs)

------------------------------------------------------------------------
-- Operations

module _ {R : Rel A p} {x y xs} where

  head : AllNeighbours R (x ∷ y ∷ xs) → R x y
  head (Rxy ∷ Rxs) = Rxy

  tail : AllNeighbours R (x ∷ y ∷ xs) → AllNeighbours R (y ∷ xs)
  tail (Rxy ∷ Rxs) = Rxs

module _ {R : Rel A p} {S : Rel A q} where

  map : R ⇒ S → AllNeighbours R ⊆ AllNeighbours S
  map R⇒S []           = []
  map R⇒S [-]          = [-]
  map R⇒S (x~xs ∷ pxs) = R⇒S x~xs ∷ map R⇒S pxs

module _ {P : Rel A p} {Q : Rel A q} {R : Rel A r} where

  zipWith : P ∩ᵇ Q ⇒ R → AllNeighbours P ∩ᵘ AllNeighbours Q ⊆ AllNeighbours R
  zipWith f ([] , [])             = []
  zipWith f ([-] , [-])           = [-]
  zipWith f (px ∷ pxs , qx ∷ qxs) = f (px , qx) ∷ zipWith f (pxs , qxs)

  unzipWith : R ⇒ P ∩ᵇ Q → AllNeighbours R ⊆ AllNeighbours P ∩ᵘ AllNeighbours Q
  unzipWith f []         = [] , []
  unzipWith f [-]        = [-] , [-]
  unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (f rx) (unzipWith f rxs)

module _ {P : Rel A p} {Q : Rel A q} where

  zip : AllNeighbours P ∩ᵘ AllNeighbours Q ⊆ AllNeighbours (P ∩ᵇ Q)
  zip = zipWith id

  unzip : AllNeighbours (P ∩ᵇ Q) ⊆ AllNeighbours P ∩ᵘ AllNeighbours Q
  unzip = unzipWith id

------------------------------------------------------------------------
-- Properties of predicates preserved by AllNeighbours

module _ {R : Rel A ℓ} where

  allNeighbours? : B.Decidable R → U.Decidable (AllNeighbours R)
  allNeighbours? R? []           = yes []
  allNeighbours? R? (x ∷ [])     = yes [-]
  allNeighbours? R? (x ∷ y ∷ xs) with R? x y | allNeighbours? R? (y ∷ xs)
  ... | yes Rxy | yes Rxs = yes (Rxy ∷ Rxs)
  ... | no ¬Rxy | _       = no (¬Rxy ∘ head)
  ... | _       | no ¬Rxs = no (¬Rxs ∘ tail)

  irrelevant : B.Irrelevant R → U.Irrelevant (AllNeighbours R)
  irrelevant irr []           []           = refl
  irrelevant irr [-]          [-]          = refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

  satisfiable : U.Satisfiable (AllNeighbours R)
  satisfiable = [] , []
