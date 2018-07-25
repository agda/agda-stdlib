------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

module Data.Vec.All.Properties where

open import Data.List using ([]; _∷_)
open import Data.List.All as List using ([]; _∷_)
open import Data.Product as Prod using (_×_; _,_; uncurry; uncurry′)
open import Data.Vec as Vec
open import Data.Vec.All as All using (All; []; _∷_)
open import Function using (_∘_; id)
open import Function.Inverse using (_↔_; inverse)
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; cong₂; →-to-⟶)

------------------------------------------------------------------------
-- map

module _ {a b p} {A : Set a} {B : Set b} {P : Pred B p} {f : A → B} where

  map⁺ : ∀ {n} {xs : Vec A n} → All (P ∘ f) xs → All P (map f xs)
  map⁺ []         = []
  map⁺ (px ∷ pxs) = px ∷ map⁺ pxs

  map⁻ : ∀ {n} {xs : Vec A n} → All P (map f xs) → All (P ∘ f) xs
  map⁻ {xs = []}    []       = []
  map⁻ {xs = _ ∷ _} (px ∷ pxs) = px ∷ map⁻ pxs

-- A variant of All.map

module _ {a b p q} {A : Set a} {B : Set b} {f : A → B}
         {P : Pred A p} {Q : Pred B q} where

  gmap : ∀ {n} → P ⋐ Q ∘ f → All P {n} ⋐ All Q {n} ∘ map f
  gmap g = map⁺ ∘ All.map g

------------------------------------------------------------------------
-- _++_

module _ {a n p} {A : Set a} {P : Pred A p} where

  ++⁺ : ∀ {m} {xs : Vec A m} {ys : Vec A n} →
        All P xs → All P ys → All P (xs ++ ys)
  ++⁺ []         pys = pys
  ++⁺ (px ∷ pxs) pys = px ∷ ++⁺ pxs pys

  ++ˡ⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
         All P (xs ++ ys) → All P xs
  ++ˡ⁻ []       _          = []
  ++ˡ⁻ (x ∷ xs) (px ∷ pxs) = px ∷ ++ˡ⁻ xs pxs

  ++ʳ⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
         All P (xs ++ ys) → All P ys
  ++ʳ⁻ []       pys        = pys
  ++ʳ⁻ (x ∷ xs) (px ∷ pxs) = ++ʳ⁻ xs pxs

  ++⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
        All P (xs ++ ys) → All P xs × All P ys
  ++⁻ []       p          = [] , p
  ++⁻ (x ∷ xs) (px ∷ pxs) = Prod.map₁ (px ∷_) (++⁻ _ pxs)

  ++⁺∘++⁻ : ∀ {m} (xs : Vec A m) {ys : Vec A n} →
            (p : All P (xs ++ ys)) →
            uncurry′ ++⁺ (++⁻ xs p) ≡ p
  ++⁺∘++⁻ []       p          = refl
  ++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = cong (px ∷_) (++⁺∘++⁻ xs pxs)

  ++⁻∘++⁺ : ∀ {m} {xs : Vec A m} {ys : Vec A n} →
            (p : All P xs × All P ys) →
            ++⁻ xs (uncurry ++⁺ p) ≡ p
  ++⁻∘++⁺ ([]       , pys) = refl
  ++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = refl

  ++↔ : ∀ {m} {xs : Vec A m} {ys : Vec A n} →
        (All P xs × All P ys) ↔ All P (xs ++ ys)
  ++↔ {xs = xs} = inverse (uncurry ++⁺) (++⁻ xs) ++⁻∘++⁺ (++⁺∘++⁻ xs)

------------------------------------------------------------------------
-- concat

module _ {a m p} {A : Set a} {P : Pred A p} where

  concat⁺ : ∀ {n} {xss : Vec (Vec A m) n} →
            All (All P) xss → All P (concat xss)
  concat⁺ []           = []
  concat⁺ (pxs ∷ pxss) = ++⁺ pxs (concat⁺ pxss)

  concat⁻ : ∀ {n} (xss : Vec (Vec A m) n) →
            All P (concat xss) → All (All P) xss
  concat⁻ []         []   = []
  concat⁻ (xs ∷ xss) pxss = ++ˡ⁻ xs pxss ∷ concat⁻ xss (++ʳ⁻ xs pxss)

------------------------------------------------------------------------
-- toList

module _ {a p} {A : Set a} {P : A → Set p} where

  toList⁺ : ∀ {n} {xs : Vec A n} → List.All P (toList xs) → All P xs
  toList⁺ {xs = []}     []         = []
  toList⁺ {xs = x ∷ xs} (px ∷ pxs) = px ∷ toList⁺ pxs

  toList⁻ : ∀ {n} {xs : Vec A n} → All P xs → List.All P (toList xs)
  toList⁻ []         = []
  toList⁻ (px ∷ pxs) = px ∷ toList⁻ pxs

------------------------------------------------------------------------
-- fromList

module _ {a p} {A : Set a} {P : A → Set p} where

  fromList⁺ : ∀ {xs} → List.All P xs → All P (fromList xs)
  fromList⁺ []         = []
  fromList⁺ (px ∷ pxs) = px ∷ fromList⁺ pxs

  fromList⁻ : ∀ {xs} → All P (fromList xs) → List.All P xs
  fromList⁻ {[]}     []         = []
  fromList⁻ {x ∷ xs} (px ∷ pxs) = px ∷ (fromList⁻ pxs)

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

All-map     = map⁺
map-All     = map⁻

All-++⁺     = ++⁺
All-++ˡ⁻    = ++ˡ⁻
All-++ʳ⁻    = ++ʳ⁻
All-++⁻     = ++⁻
All-++⁺∘++⁻ = ++⁺∘++⁻
All-++⁻∘++⁺ = ++⁻∘++⁺

All-concat⁺ = concat⁺
All-concat⁻ = concat⁻
