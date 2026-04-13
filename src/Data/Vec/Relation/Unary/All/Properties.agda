------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Relation.Unary.All.Properties where

open import Data.Nat.Base using (ℕ; zero; suc; _+_)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.List.Relation.Unary.All as List using ([]; _∷_)
open import Data.Product.Base as Product using (_×_; _,_; uncurry; uncurry′)
open import Data.Vec.Base as Vec using (Vec; []; _∷_; map; _++_; concat;
  tabulate; drop; take; toList; fromList)
open import Data.Vec.Relation.Unary.All as All using (All; []; _∷_)
open import Level using (Level)
open import Function.Base using (_∘_; id)
open import Function.Bundles using (_↔_; mk↔ₛ′)
open import Relation.Unary using (Pred) renaming (_⊆_ to _⋐_)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; cong; cong₂)

private
  variable
    a b p q : Level
    A : Set a
    B : Set b
    P : Pred A p
    Q : Pred B q
    m n : ℕ
    xs : Vec A n

------------------------------------------------------------------------
-- lookup

lookup⁺ : All P xs → ∀ i → P (Vec.lookup xs i)
lookup⁺ (px ∷ _)  zero    = px
lookup⁺ (_ ∷ pxs) (suc i) = lookup⁺ pxs i

lookup⁻ : (∀ i → P (Vec.lookup xs i)) → All P xs
lookup⁻ {xs = []}    pxs = []
lookup⁻ {xs = _ ∷ _} pxs = pxs zero ∷ lookup⁻ (pxs ∘ suc)

------------------------------------------------------------------------
-- map

map⁺ : {f : A → B} → All (P ∘ f) xs → All P (map f xs)
map⁺ []         = []
map⁺ (px ∷ pxs) = px ∷ map⁺ pxs

map⁻ : {f : A → B} → All P (map f xs) → All (P ∘ f) xs
map⁻ {xs = []}    []       = []
map⁻ {xs = _ ∷ _} (px ∷ pxs) = px ∷ map⁻ pxs

-- A variant of All.map

gmap : {f : A → B} → P ⋐ Q ∘ f → All P {n} ⋐ All Q {n} ∘ map f
gmap g = map⁺ ∘ All.map g

------------------------------------------------------------------------
-- _++_

++⁺ : {xs : Vec A m} {ys : Vec A n} →
      All P xs → All P ys → All P (xs ++ ys)
++⁺ []         pys = pys
++⁺ (px ∷ pxs) pys = px ∷ ++⁺ pxs pys

++ˡ⁻ : (xs : Vec A m) {ys : Vec A n} →
       All P (xs ++ ys) → All P xs
++ˡ⁻ []       _          = []
++ˡ⁻ (x ∷ xs) (px ∷ pxs) = px ∷ ++ˡ⁻ xs pxs

++ʳ⁻ : (xs : Vec A m) {ys : Vec A n} →
       All P (xs ++ ys) → All P ys
++ʳ⁻ []       pys        = pys
++ʳ⁻ (x ∷ xs) (px ∷ pxs) = ++ʳ⁻ xs pxs

++⁻ : (xs : Vec A m) {ys : Vec A n} →
      All P (xs ++ ys) → All P xs × All P ys
++⁻ []       p          = [] , p
++⁻ (x ∷ xs) (px ∷ pxs) = Product.map₁ (px ∷_) (++⁻ _ pxs)

++⁺∘++⁻ : (xs : Vec A m) {ys : Vec A n} →
          (p : All P (xs ++ ys)) →
          uncurry′ ++⁺ (++⁻ xs p) ≡ p
++⁺∘++⁻ []       p          = refl
++⁺∘++⁻ (x ∷ xs) (px ∷ pxs) = cong (px ∷_) (++⁺∘++⁻ xs pxs)

++⁻∘++⁺ : {xs : Vec A m} {ys : Vec A n} →
          (p : All P xs × All P ys) →
          ++⁻ xs (uncurry ++⁺ p) ≡ p
++⁻∘++⁺ ([]       , pys) = refl
++⁻∘++⁺ (px ∷ pxs , pys) rewrite ++⁻∘++⁺ (pxs , pys) = refl

++↔ : {xs : Vec A m} {ys : Vec A n} →
      (All P xs × All P ys) ↔ All P (xs ++ ys)
++↔ {xs = xs} = mk↔ₛ′ (uncurry ++⁺) (++⁻ xs) (++⁺∘++⁻ xs) ++⁻∘++⁺

------------------------------------------------------------------------
-- concat

concat⁺ : {xss : Vec (Vec A m) n} →
          All (All P) xss → All P (concat xss)
concat⁺ []           = []
concat⁺ (pxs ∷ pxss) = ++⁺ pxs (concat⁺ pxss)

concat⁻ : (xss : Vec (Vec A m) n) →
          All P (concat xss) → All (All P) xss
concat⁻ []         []   = []
concat⁻ (xs ∷ xss) pxss = ++ˡ⁻ xs pxss ∷ concat⁻ xss (++ʳ⁻ xs pxss)

------------------------------------------------------------------------
-- swap

module _ {_~_ : REL A B p} where

  All-swap : ∀ {n m xs ys} →
             All (λ x → All (x ~_) ys) {n} xs →
             All (λ y → All (_~ y) xs) {m} ys
  All-swap {ys = []}     _   = []
  All-swap {ys = y ∷ ys} []  = All.universal (λ _ → []) (y ∷ ys)
  All-swap {ys = y ∷ ys} ((x~y ∷ x~ys) ∷ pxs) =
    (x~y ∷ (All.map All.head pxs)) ∷
    All-swap (x~ys ∷ (All.map All.tail pxs))


------------------------------------------------------------------------
-- tabulate

module _ {P : A → Set p} where

  tabulate⁺ : ∀ {n} {f : Fin n → A} →
              (∀ i → P (f i)) → All P (tabulate f)
  tabulate⁺ {zero}  Pf = []
  tabulate⁺ {suc n} Pf = Pf zero ∷ tabulate⁺ (Pf ∘ suc)

  tabulate⁻ : ∀ {n} {f : Fin n → A} →
              All P (tabulate f) → (∀ i → P (f i))
  tabulate⁻ (px ∷ _) zero    = px
  tabulate⁻ (_ ∷ pf) (suc i) = tabulate⁻ pf i

------------------------------------------------------------------------
-- take and drop

drop⁺ : ∀ m {xs} → All P {m + n} xs → All P {n} (drop m xs)
drop⁺ zero pxs = pxs
drop⁺ (suc m) {x ∷ xs} (px ∷ pxs) = drop⁺ m pxs

take⁺ : ∀ m {xs} → All P {m + n} xs → All P {m} (take m xs)
take⁺ zero pxs = []
take⁺ (suc m) {x ∷ xs} (px ∷ pxs) = px ∷ take⁺ m pxs

------------------------------------------------------------------------
-- toList

module _ {P : Pred A p} where

  toList⁺ : ∀ {n} {xs : Vec A n} → All P xs → List.All P (toList xs)
  toList⁺ []         = []
  toList⁺ (px ∷ pxs) = px ∷ toList⁺ pxs

  toList⁻ : ∀ {n} {xs : Vec A n} → List.All P (toList xs) → All P xs
  toList⁻ {xs = []}     []         = []
  toList⁻ {xs = x ∷ xs} (px ∷ pxs) = px ∷ toList⁻ pxs

------------------------------------------------------------------------
-- fromList

module _ {P : Pred A p} where

  fromList⁺ : ∀ {xs} → List.All P xs → All P (fromList xs)
  fromList⁺ []         = []
  fromList⁺ (px ∷ pxs) = px ∷ fromList⁺ pxs

  fromList⁻ : ∀ {xs} → All P (fromList xs) → List.All P xs
  fromList⁻ {[]}     []         = []
  fromList⁻ {x ∷ xs} (px ∷ pxs) = px ∷ (fromList⁻ pxs)
