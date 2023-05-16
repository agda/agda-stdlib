------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where every consecutative pair of elements is related.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Unary.Linked {a} {A : Set a} where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product as Prod using (_,_; _×_; uncurry; <_,_>)
open import Function.Base using (id; _∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary as B using (Rel; _⇒_)
open import Relation.Binary.Construct.Intersection renaming (_∩_ to _∩ᵇ_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary as U renaming (_∩_ to _∩ᵘ_) hiding (_⇒_)
open import Relation.Nullary.Decidable as Dec using (yes; no; _×-dec_; map′)

private
  variable
    p q r s ℓ : Level
    P : Rel A p
    Q : Rel A q
    R : Rel A r
    S : Rel A s
    n : ℕ

------------------------------------------------------------------------
-- Definition

-- Linked R xs means that every consecutative pair of elements in xs is
-- a member of relation R.

infixr 5 _∷_

data Linked (R : Rel A ℓ) : Vec A n → Set (a ⊔ ℓ) where
  []  : Linked R []
  [-] : ∀ {x} → Linked R (x ∷ [])
  _∷_ : ∀ {x} {xs : Vec A (suc n)} → R x (Vec.head xs) → Linked R xs → Linked R (x ∷ xs)

------------------------------------------------------------------------
-- Operations

head : ∀ {x} {xs : Vec A (suc n)} → Linked R (x ∷ xs) → R x (Vec.head xs)
head (Rxy ∷ Rxs) = Rxy

tail : ∀ {xs : Vec A (suc n)} → Linked R xs → Linked R (Vec.tail xs)
tail [-]       = []
tail (_ ∷ Rxs) = Rxs

map : R ⇒ S → Linked R {n} ⊆ Linked S
map R⇒S []           = []
map R⇒S [-]          = [-]
map R⇒S (x~xs ∷ pxs) = R⇒S x~xs ∷ map R⇒S pxs

zipWith : P ∩ᵇ Q ⇒ R → Linked P {n} ∩ᵘ Linked Q ⊆ Linked R
zipWith f ([] , [])             = []
zipWith f ([-] , [-])           = [-]
zipWith f (px ∷ pxs , qx ∷ qxs) = f (px , qx) ∷ zipWith f (pxs , qxs)

unzipWith : R ⇒ P ∩ᵇ Q → Linked R {n} ⊆ Linked P ∩ᵘ Linked Q
unzipWith f []         = [] , []
unzipWith f [-]        = [-] , [-]
unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (f rx) (unzipWith f rxs)

zip : Linked P {n} ∩ᵘ Linked Q ⊆ Linked (P ∩ᵇ Q)
zip = zipWith id

unzip : Linked (P ∩ᵇ Q) {n} ⊆ Linked P ∩ᵘ Linked Q
unzip = unzipWith id

------------------------------------------------------------------------
-- Properties of predicates preserved by Linked

linked? : B.Decidable R → U.Decidable (Linked R {n})
linked? R? []           = yes []
linked? R? (x ∷ [])     = yes [-]
linked? R? (x ∷ y ∷ xs) =
  map′ (uncurry _∷_) < head , tail > (R? x y ×-dec linked? R? (y ∷ xs))

irrelevant : B.Irrelevant R → U.Irrelevant (Linked R {n})
irrelevant irr []           []           = refl
irrelevant irr [-]          [-]          = refl
irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
  cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

satisfiable : U.Satisfiable (Linked R)
satisfiable = [] , []
