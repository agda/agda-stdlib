------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where all elements and their tails satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Level using (Level; _⊔_)
open import Function using (_∘_)
open import Data.Nat as ℕ using (ℕ)
open import Data.Vec.Base as Vec using (Vec; _∷_; [])
open import Data.Fin.Base as Fin using (Fin; zero; suc)
open import Data.Product as Prod using (_×_; _,_; <_,_>; uncurry)
open import Relation.Nullary using (Dec; yes)
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Nullary.Decidable using (map′)
open import Relation.Unary using (_⊆_; _∩_; Decidable; Universal; Irrelevant)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)


module Data.Vec.Relation.Unary.AllCons where

private
  variable
    a b c p q r ℓ ℓ₁ ℓ₂ : Level
    A B C : Set a

infixr 5 _∷_

ConsP : Set a → (ℓ : Level) → Set _
ConsP A ℓ = (a : A) → {n : ℕ} → Vec A n → Set ℓ

data AllCons {a} {A : Set a} (P : ConsP A p) : ∀ {n} → Vec A n → Set (a ⊔ p) where
  []  : AllCons P []
  _∷_ : ∀ {n x} {xs : Vec A n} (px : P x xs) (pxs : AllCons P xs) → AllCons P (x ∷ xs)

module _ {P : ConsP A p} where
  head : ∀ {n x} {xs : Vec A n} → AllCons P (x ∷ xs) → P x xs
  head (px ∷ pxs) = px

  tail : ∀ {n x} {xs : Vec A n} → AllCons P (x ∷ xs) → AllCons P xs
  tail (px ∷ pxs) = pxs

  uncons : ∀ {n x} {xs : Vec A n} → AllCons P (x ∷ xs) → P x xs × AllCons P xs
  uncons = < head , tail >

  lookup : ∀ {n} {xs : Vec A n} (i : Fin n) →
           AllCons P xs → P (Vec.lookup xs i) (Vec.drop′ (suc i) xs)
  lookup zero    (px ∷ pxs) = px
  lookup (suc i) (px ∷ pxs) = lookup i pxs

  tabulate : ∀ {n xs} → (∀ i → P (Vec.lookup xs i) (Vec.drop′ (suc i) xs)) →
             AllCons P {n} xs
  tabulate {xs = []} f = []
  tabulate {xs = x ∷ xs} f = f zero ∷ tabulate (f ∘ suc)

  module _ {c} {C : Set c} where
    toVec : ∀ {n} {xs : Vec A n} → (∀ {n x} {xs : Vec A n} → P x xs → C) → AllCons P xs → Vec C n
    toVec f [] = []
    toVec f (x ∷ ps) = f x ∷ toVec f ps

module _ where
  _⇒_ : ConsP A ℓ₁ → ConsP A ℓ₂ → Set _
  P ⇒ Q = ∀ {x n} {xs : Vec _ n} → P x xs → Q x xs

  _×ₐ_ : ConsP A ℓ₁ → ConsP A ℓ₂ → ConsP A _
  P ×ₐ Q = λ x xs → P x xs × Q x xs

  Decidableₐ : ConsP A ℓ → Set _
  Decidableₐ P = ∀ x {n} (xs : Vec _ n) → Dec (P x xs)

  Universalₐ : ConsP A ℓ → Set _
  Universalₐ P = ∀ x {n} (xs : Vec _ n) → P x xs

  Irrelevantₐ : ConsP A ℓ → Set _
  Irrelevantₐ P = ∀ {x n} {xs : Vec _ n} (a b : P x xs) → a ≡ b

module _ {P : ConsP A p} {Q : ConsP A q} where

  map : ∀ {n} → P ⇒ Q → AllCons P {n} ⊆ AllCons Q {n}
  map g []         = []
  map g (px ∷ pxs) = g px ∷ map g pxs

  zip : ∀ {n} → AllCons P ∩ AllCons Q ⊆ AllCons (P ×ₐ Q) {n}
  zip ([] , [])             = []
  zip (px ∷ pxs , qx ∷ qxs) = (px , qx) ∷ zip (pxs , qxs)

  unzip : ∀ {n} → AllCons (P ×ₐ Q) {n} ⊆ AllCons P ∩ AllCons Q
  unzip []           = [] , []
  unzip (pqx ∷ pqxs) = Prod.zip _∷_ _∷_ pqx (unzip pqxs)

module _ {P : ConsP A p} {Q : ConsP B q} {R : ConsP C r} where

  zipWith : ∀ {_⊕_ : A → B → C} →
            (∀ {x y} {n} {xs : Vec A n} {ys} → P x xs → Q y ys → R (x ⊕ y) (Vec.zipWith _⊕_ xs ys)) →
            ∀ {n xs ys} → AllCons P {n} xs → AllCons Q {n} ys →
            AllCons R {n} (Vec.zipWith _⊕_ xs ys)
  zipWith _⊕_ {xs = []}     {[]}     []         []         = []
  zipWith _⊕_ {xs = x ∷ xs} {y ∷ ys} (px ∷ pxs) (qy ∷ qys) =
    px ⊕ qy ∷ zipWith _⊕_ pxs qys

------------------------------------------------------------------------
-- Properties of predicates preserved by AllCons

module _ {P : ConsP A p} where

  all : ∀ {n} → Decidableₐ P → Decidable (AllCons P {n})
  all P? []       = yes []
  all P? (x ∷ xs) = map′ (uncurry _∷_) uncons (P? x xs ×-dec all P? xs)

  universal : Universalₐ P → ∀ {n} → Universal (AllCons P {n})
  universal u []       = []
  universal u (x ∷ xs) = u x xs ∷ universal u xs

  irrelevant : Irrelevantₐ P → ∀ {n} → Irrelevant (AllCons P {n})
  irrelevant irr []           []           = refl
  irrelevant irr (px₁ ∷ pxs₁) (px₂ ∷ pxs₂) =
    cong₂ _∷_ (irr px₁ px₂) (irrelevant irr pxs₁ pxs₂)
