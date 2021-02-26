------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where every consecutative pair of elements is related.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.Linked {a} {A : Set a} where

open import Data.Fin.Base using (zero; suc)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Product as Prod using (_,_; _×_; uncurry; <_,_>)
open import Data.Maybe.Base using (just)
open import Data.Maybe.Relation.Binary.Connected
  using (Connected; just; just-nothing)
open import Function.Base using (id; _∘_)
open import Level using (Level; _⊔_)
open import Relation.Binary as B using (Rel; _⇒_; Transitive)
open import Relation.Binary.Construct.Intersection renaming (_∩_ to _∩ᵇ_)
open import Relation.Binary.PropositionalEquality
open import Relation.Unary as U renaming (_∩_ to _∩ᵘ_) hiding (_⇒_)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable as Dec using (map′)
open import Relation.Nullary.Product using (_×-dec_)

private
  variable
    p q r ℓ : Level
    R S T : Rel A ℓ
    x y : A
    xs ys : List A

------------------------------------------------------------------------
-- Definition

-- Linked R xs means that every consecutative pair of elements in xs is
-- a member of relation R.

infixr 5 _∷_

data Linked (R : Rel A ℓ) : List A → Set (a ⊔ ℓ) where
  []  : Linked R []
  [-] : ∀ {x} → Linked R (x ∷ [])
  _∷_ : ∀ {x y xs} → R x y → Linked R (y ∷ xs) → Linked R (x ∷ y ∷ xs)

------------------------------------------------------------------------
-- Operations

head : Linked R (x ∷ y ∷ xs) → R x y
head (Rxy ∷ Rxs) = Rxy

head′ : Linked R (x ∷ xs) → Connected R (just x) (List.head xs)
head′ [-]       = just-nothing
head′ (Rxy ∷ _) = just Rxy

tail : Linked R (x ∷ xs) → Linked R xs
tail [-]       = []
tail (_ ∷ Rxs) = Rxs

infixr 5 _∷′_
_∷′_ : Connected R (just x) (List.head xs) →
       Linked R xs →
       Linked R (x ∷ xs)
_∷′_ {xs = []}     _  _            = [-]
_∷′_ {xs = y ∷ xs} (just Rxy) Ryxs = Rxy ∷ Ryxs

map : R ⇒ S → Linked R ⊆ Linked S
map R⇒S []           = []
map R⇒S [-]          = [-]
map R⇒S (x~xs ∷ pxs) = R⇒S x~xs ∷ map R⇒S pxs

zipWith : R ∩ᵇ S ⇒ T → Linked R ∩ᵘ Linked S ⊆ Linked T
zipWith f ([] , [])             = []
zipWith f ([-] , [-])           = [-]
zipWith f (px ∷ pxs , qx ∷ qxs) = f (px , qx) ∷ zipWith f (pxs , qxs)

unzipWith : R ⇒ S ∩ᵇ T → Linked R ⊆ Linked S ∩ᵘ Linked T
unzipWith f []         = [] , []
unzipWith f [-]        = [-] , [-]
unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (f rx) (unzipWith f rxs)

zip : Linked R ∩ᵘ Linked S ⊆ Linked (R ∩ᵇ S)
zip = zipWith id

unzip : Linked (R ∩ᵇ S) ⊆ Linked R ∩ᵘ Linked S
unzip = unzipWith id

lookup : Transitive R → Linked R xs →
         Connected R (just x) (List.head xs) →
         ∀ i → R x (List.lookup xs i)
lookup trans [-]       (just Rvx) zero    = Rvx
lookup trans (x ∷ xs↗) (just Rvx) zero    = Rvx
lookup trans (x ∷ xs↗) (just Rvx) (suc i) =
  lookup trans xs↗ (just (trans Rvx x)) i

------------------------------------------------------------------------
-- Properties of predicates preserved by Linked

linked? : B.Decidable R → U.Decidable (Linked R)
linked? R? []           = yes []
linked? R? (x ∷ [])     = yes [-]
linked? R? (x ∷ y ∷ xs) =
  map′ (uncurry _∷_) < head , tail > (R? x y ×-dec linked? R? (y ∷ xs))

irrelevant : B.Irrelevant R → U.Irrelevant (Linked R)
irrelevant irr []           []           = refl
irrelevant irr [-]          [-]          = refl
irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
  cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

satisfiable : U.Satisfiable (Linked R)
satisfiable = [] , []
