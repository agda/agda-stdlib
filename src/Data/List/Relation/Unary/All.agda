------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.List.Relation.Unary.All where

open import Category.Applicative
open import Category.Monad
open import Data.Empty using (⊥)
open import Data.List.Base as List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional renaming (_∈_ to _∈ₚ_)
import Data.List.Membership.Setoid as SetoidMembership
open import Data.Product as Prod
  using (∃; -,_; _×_; _,_; proj₁; proj₂; uncurry)
open import Function
open import Level
open import Relation.Nullary hiding (Irrelevant)
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary using (Setoid; _Respects_)
open import Relation.Binary.PropositionalEquality as P

private
  variable
    a b p q r ℓ : Level
    A : Set a
    B : Set b

------------------------------------------------------------------------
-- Definitions

-- Given a predicate P, then All P xs means that every element in xs
-- satisfies P. See `Relation.Unary` for an explanation of predicates.

infixr 5 _∷_

data All {A : Set a} (P : Pred A p) : Pred (List A) (a ⊔ p) where
  []  : All P []
  _∷_ : ∀ {x xs} (px : P x) (pxs : All P xs) → All P (x ∷ xs)

-- All P xs is a finite map from indices x ∈ xs to content P x.
-- Relation pxs [ i ]= px states that, in map pxs, key i : x ∈ xs points to value px.

infix 4 _[_]=_

data _[_]=_ {A : Set a} {P : Pred A p} :
            ∀ {x xs} → All P xs → x ∈ₚ xs → P x → Set (a ⊔ p) where

  here  : ∀ {x xs} {px : P x} {pxs : All P xs} →
          px ∷ pxs [ here refl ]= px

  there : ∀ {x xs y} {px : P x} {pxs : All P xs} {py : P y} {i : x ∈ₚ xs} →
          pxs [ i ]= px →
          py ∷ pxs [ there i ]= px

-- A list is empty if having an element is impossible.

Null : Pred (List A) _
Null = All (λ _ → ⊥)

------------------------------------------------------------------------
-- Operations on All

module _ {P : Pred A p} where

  uncons : ∀ {x xs} → All P (x ∷ xs) → P x × All P xs
  uncons (px ∷ pxs) = px , pxs

  head : ∀ {x xs} → All P (x ∷ xs) → P x
  head = proj₁ ∘ uncons

  tail : ∀ {x xs} → All P (x ∷ xs) → All P xs
  tail = proj₂ ∘ uncons

  reduce : (f : ∀ {x} → P x → B) → ∀ {xs} → All P xs → List B
  reduce f []         = []
  reduce f (px ∷ pxs) = f px ∷ reduce f pxs

  construct : (f : B → ∃ P) (xs : List B) → ∃ (All P)
  construct f []       = [] , []
  construct f (x ∷ xs) = Prod.zip _∷_ _∷_ (f x) (construct f xs)

  fromList : (xs : List (∃ P)) → All P (List.map proj₁ xs)
  fromList []              = []
  fromList ((x , p) ∷ xps) = p ∷ fromList xps

  toList : ∀ {xs} → All P xs → List (∃ P)
  toList pxs = reduce (λ {x} px → x , px) pxs

module _ {P : Pred A p} {Q : Pred A q} where

  map : P ⊆ Q → All P ⊆ All Q
  map g []         = []
  map g (px ∷ pxs) = g px ∷ map g pxs

module _ {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

  zipWith : P ∩ Q ⊆ R → All P ∩ All Q ⊆ All R
  zipWith f ([] , [])             = []
  zipWith f (px ∷ pxs , qx ∷ qxs) = f (px , qx) ∷ zipWith f (pxs , qxs)

  unzipWith : R ⊆ P ∩ Q → All R ⊆ All P ∩ All Q
  unzipWith f []         = [] , []
  unzipWith f (rx ∷ rxs) = Prod.zip _∷_ _∷_ (f rx) (unzipWith f rxs)

module _ {P : Pred A p} {Q : Pred A q} where

  zip : All P ∩ All Q ⊆ All (P ∩ Q)
  zip = zipWith id

  unzip : All (P ∩ Q) ⊆ All P ∩ All Q
  unzip = unzipWith id

module _(S : Setoid a ℓ) {P : Pred (Setoid.Carrier S) p} where
  open Setoid S renaming (Carrier to C; refl to refl₁)
  open SetoidMembership S

  tabulateₛ : ∀ {xs} → (∀ {x} → x ∈ xs → P x) → All P xs
  tabulateₛ {[]}     hyp = []
  tabulateₛ {x ∷ xs} hyp = hyp (here refl₁) ∷ tabulateₛ (hyp ∘ there)

module _ {P : Pred A p} where

  tabulate : ∀ {xs} → (∀ {x} → x ∈ₚ xs → P x) → All P xs
  tabulate = tabulateₛ (P.setoid A)

self : ∀ {xs : List A} → All (const A) xs
self = tabulate (λ {x} _ → x)

------------------------------------------------------------------------
-- (weak) updateAt

module _ {P : Pred A p} where

  infixl 6 _[_]%=_ _[_]≔_

  updateAt : ∀ {x xs} → x ∈ₚ xs → (P x → P x) → All P xs → All P xs
  updateAt () f []
  updateAt (here refl) f (px ∷ pxs) = f px ∷ pxs
  updateAt (there i)   f (px ∷ pxs) =   px ∷ updateAt i f pxs

  _[_]%=_ : ∀ {x xs} → All P xs → x ∈ₚ xs → (P x → P x) → All P xs
  pxs [ i ]%= f = updateAt i f pxs

  _[_]≔_ : ∀ {x xs} → All P xs → x ∈ₚ xs → P x → All P xs
  pxs [ i ]≔ px = pxs [ i ]%= const px

------------------------------------------------------------------------
-- Traversable-like functions

module _ (p : Level) {A : Set a} {P : Pred A (a ⊔ p)}
         {F : Set (a ⊔ p) → Set (a ⊔ p)}
         (App : RawApplicative F)
         where

  open RawApplicative App

  sequenceA : All (F ∘′ P) ⊆ F ∘′ All P
  sequenceA []       = pure []
  sequenceA (x ∷ xs) = _∷_ <$> x ⊛ sequenceA xs

  mapA : ∀ {Q : Pred A q} → (Q ⊆ F ∘′ P) → All Q ⊆ (F ∘′ All P)
  mapA f = sequenceA ∘′ map f

  forA : ∀ {Q : Pred A q} {xs} → All Q xs → (Q ⊆ F ∘′ P) → F (All P xs)
  forA qxs f = mapA f qxs

module _ (p : Level) {A : Set a} {P : Pred A (a ⊔ p)}
         {M : Set (a ⊔ p) → Set (a ⊔ p)}
         (Mon : RawMonad M)
         where

  private App = RawMonad.rawIApplicative Mon

  sequenceM : All (M ∘′ P) ⊆ M ∘′ All P
  sequenceM = sequenceA p App

  mapM : ∀ {Q : Pred A q} → (Q ⊆ M ∘′ P) → All Q ⊆ (M ∘′ All P)
  mapM = mapA p App

  forM : ∀ {Q : Pred A q} {xs} → All Q xs → (Q ⊆ M ∘′ P) → M (All P xs)
  forM = forA p App

------------------------------------------------------------------------
-- Generalised lookup based on a proof of Any

module _ {P : Pred A p} {Q : Pred A q} where

  lookupAny : ∀ {xs} → All P xs → (i : Any Q xs) → (P ∩ Q) (Any.lookup i)
  lookupAny (px ∷ pxs) (here qx) = px , qx
  lookupAny (px ∷ pxs) (there i) = lookupAny pxs i

module _ {P : Pred A p} {Q : Pred A q} {R : Pred A r} where

  lookupWith : ∀[ P ⇒ Q ⇒ R ] → ∀ {xs} → All P xs → (i : Any Q xs) →
               R (Any.lookup i)
  lookupWith f pxs i = Prod.uncurry f (lookupAny pxs i)

module _ {P : Pred A p} where

  lookup : ∀ {xs} → All P xs → (∀ {x} → x ∈ₚ xs → P x)
  lookup pxs = lookupWith (λ { px refl → px }) pxs

------------------------------------------------------------------------
-- Properties of predicates preserved by All

module _ {P : Pred A p} where

  all : Decidable P → Decidable (All P)
  all p []       = yes []
  all p (x ∷ xs) = Dec.map′ (uncurry _∷_) uncons (p x ×-dec all p xs)

  universal : Universal P → Universal (All P)
  universal u []       = []
  universal u (x ∷ xs) = u x ∷ universal u xs

  irrelevant : Irrelevant P → Irrelevant (All P)
  irrelevant irr []           []           = P.refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    P.cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)

  satisfiable : Satisfiable (All P)
  satisfiable = [] , []
