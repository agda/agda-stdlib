------------------------------------------------------------------------
-- The Agda standard library
--
-- Vectors where all elements satisfy a given property
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Relation.Unary.All where

open import Data.Nat.Base using (ℕ; zero; suc; NonZero)
open import Data.Product as Prod using (_×_; _,_; uncurry; <_,_>)
open import Data.Sum.Base as Sum using (inj₁; inj₂)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Data.Vec.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Vec.Membership.Propositional renaming (_∈_ to _∈ₚ_)
import Data.Vec.Membership.Setoid as SetoidMembership
open import Function.Base using (_∘_)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Decidable as Dec using (_×-dec_; yes; no)
open import Relation.Unary hiding (_∈_)
open import Relation.Binary using (Setoid; _Respects_)
open import Relation.Binary.PropositionalEquality.Core as P using (subst)

private
  variable
    a b c p q r ℓ : Level
    A : Set a
    B : Set b
    C : Set c
    P : Pred A p
    Q : Pred A q
    R : Pred A r
    n : ℕ
    x : A
    xs : Vec A n

------------------------------------------------------------------------
-- All P xs means that all elements in xs satisfy P.

infixr 5 _∷_

data All {A : Set a} (P : Pred A p) : Vec A n → Set (p ⊔ a) where
  []  : All P []
  _∷_ : (px : P x) (pxs : All P xs) → All P (x ∷ xs)

------------------------------------------------------------------------
-- Operations on All

head : All P (x ∷ xs) → P x
head (px ∷ pxs) = px

tail : All P (x ∷ xs) → All P xs
tail (px ∷ pxs) = pxs

reduce : (f : ∀ {x} → P x → B) → ∀ {n} {xs : Vec A n} → All P xs → Vec B n
reduce f []         = []
reduce f (px ∷ pxs) = f px ∷ reduce f pxs

uncons : All P (x ∷ xs) → P x × All P xs
uncons = < head , tail >

map : P ⊆ Q → All P ⊆ All Q {n}
map g []         = []
map g (px ∷ pxs) = g px ∷ map g pxs

zip : All P ∩ All Q ⊆ All (P ∩ Q) {n}
zip ([] , [])             = []
zip (px ∷ pxs , qx ∷ qxs) = (px , qx) ∷ zip (pxs , qxs)

unzip : All (P ∩ Q) {n} ⊆ All P ∩ All Q
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
-- Generalised lookup based on a proof of Any

lookupAny : All P xs → (i : Any Q xs) → (P ∩ Q) (Any.lookup i)
lookupAny (px ∷ pxs) (here qx) = px , qx
lookupAny (px ∷ pxs) (there i) = lookupAny pxs i

lookupWith : ∀[ P ⇒ Q ⇒ R ] → All P xs → (i : Any Q xs) → R (Any.lookup i)
lookupWith f pxs i = Prod.uncurry f (lookupAny pxs i)

lookup : All P xs → (∀ {x} → x ∈ₚ xs → P x)
lookup pxs = lookupWith (λ { px P.refl → px }) pxs

module _(S : Setoid a ℓ) {P : Pred (Setoid.Carrier S) p} where
  open Setoid S renaming (sym to sym₁)
  open SetoidMembership S

  lookupₛ : P Respects _≈_ → All P xs → (∀ {x} → x ∈ xs → P x)
  lookupₛ resp pxs = lookupWith (λ py x=y → resp (sym₁ x=y) py) pxs

------------------------------------------------------------------------
-- Properties of predicates preserved by All

all? : ∀ {n} → Decidable P → Decidable (All P {n})
all? P? []       = yes []
all? P? (x ∷ xs) = Dec.map′ (uncurry _∷_) uncons (P? x ×-dec all? P? xs)

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

------------------------------------------------------------------------
-- Generalised decidability procedure

decide :  Π[ P ∪ Q ] → Π[ All P {n} ∪ Any Q ]
decide p∪q [] = inj₁ []
decide p∪q (x ∷ xs) with p∪q x
... | inj₂ qx = inj₂ (here qx)
... | inj₁ px = Sum.map (px ∷_) there (decide p∪q xs)


all = all?
{-# WARNING_ON_USAGE all
"Warning: all was deprecated in v1.4.
Please use all? instead."
#-}
