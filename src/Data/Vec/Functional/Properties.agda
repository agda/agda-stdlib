------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc; toℕ; fromℕ<; reduce≥;
  _↑ˡ_; _↑ʳ_; punchIn; punchOut)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc)
import Data.Nat.Properties as ℕ
open import Data.Product.Base as Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base as List using (List)
import Data.List.Properties as List
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec.Base as Vec using (Vec)
import Data.Vec.Properties as Vec
open import Data.Vec.Functional using (Vector; head; tail; updateAt;
  map; _++_; insertAt; removeAt; toVec; fromVec; toList; fromList)
open import Function.Base using (_∘_; id)
open import Level using (Level)
open import Relation.Binary.Definitions using (DecidableEquality; Decidable)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; _≗_; refl; _≢_; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (module ≡-Reasoning)
open import Relation.Nullary.Decidable
  using (Dec; does; yes; no; map′; _×-dec_)

import Data.Fin.Properties as Finₚ

private
  variable
    a b c : Level
    A B C : Set a
    m n : ℕ

------------------------------------------------------------------------

module _ {xs ys : Vector A (suc n)} where

  ∷-cong : head xs ≡ head ys → tail xs ≗ tail ys → xs ≗ ys
  ∷-cong eq _ zero    = eq
  ∷-cong _ eq (suc i) = eq i

  ∷-injective : xs ≗ ys → head xs ≡ head ys × tail xs ≗ tail ys
  ∷-injective eq = eq zero , eq ∘ suc

≗-dec : DecidableEquality A → Decidable {A = Vector A n} _≗_
≗-dec {n = zero}  _≟_ xs ys = yes λ ()
≗-dec {n = suc n} _≟_ xs ys =
  map′ (Product.uncurry ∷-cong) ∷-injective
       (head xs ≟ head ys ×-dec ≗-dec _≟_ (tail xs) (tail ys))

------------------------------------------------------------------------
-- updateAt

-- (+) updateAt i actually updates the element at index i.

updateAt-updates : ∀ (i : Fin n) {f : A → A} (xs : Vector A n) →
                   updateAt xs i f i ≡ f (xs i)
updateAt-updates zero    xs = refl
updateAt-updates (suc i) xs = updateAt-updates i (tail xs)

-- (-) updateAt i does not touch the elements at other indices.

updateAt-minimal : ∀ (i j : Fin n) {f : A → A} (xs : Vector A n) →
                   i ≢ j → updateAt xs j f i ≡ xs i
updateAt-minimal zero    zero    xs 0≢0 = ⊥-elim (0≢0 refl)
updateAt-minimal zero    (suc j) xs _   = refl
updateAt-minimal (suc i) zero    xs _   = refl
updateAt-minimal (suc i) (suc j) xs i≢j = updateAt-minimal i j (tail xs) (i≢j ∘ cong suc)

-- updateAt i is a monoid morphism from A → A to Vector A n → Vector A n.

updateAt-id-local : ∀ (i : Fin n) {f : A → A} (xs : Vector A n) →
                    f (xs i) ≡ xs i →
                    updateAt xs i f ≗ xs
updateAt-id-local zero    xs eq zero    = eq
updateAt-id-local zero    xs eq (suc j) = refl
updateAt-id-local (suc i) xs eq zero    = refl
updateAt-id-local (suc i) xs eq (suc j) = updateAt-id-local i (tail xs) eq j

updateAt-id : ∀ (i : Fin n) (xs : Vector A n) →
              updateAt xs i id ≗ xs
updateAt-id i xs = updateAt-id-local i xs refl

updateAt-updateAt-local : ∀ (i : Fin n) {f g h : A → A} (xs : Vector A n) →
                          f (g (xs i)) ≡ h (xs i) →
                          updateAt (updateAt xs i g) i f ≗ updateAt xs i h
updateAt-updateAt-local zero    xs eq zero    = eq
updateAt-updateAt-local zero    xs eq (suc j) = refl
updateAt-updateAt-local (suc i) xs eq zero    = refl
updateAt-updateAt-local (suc i) xs eq (suc j) = updateAt-updateAt-local i (tail xs) eq j

updateAt-updateAt : ∀ (i : Fin n) {f g : A → A} (xs : Vector A n) →
                    updateAt (updateAt xs i g) i f ≗ updateAt xs i (f ∘ g)
updateAt-updateAt i xs = updateAt-updateAt-local i xs refl

updateAt-cong-local : ∀ (i : Fin n) {f g : A → A} (xs : Vector A n) →
                      f (xs i) ≡ g (xs i) →
                      updateAt xs i f ≗ updateAt xs i g
updateAt-cong-local zero    xs eq zero    = eq
updateAt-cong-local zero    xs eq (suc j) = refl
updateAt-cong-local (suc i) xs eq zero    = refl
updateAt-cong-local (suc i) xs eq (suc j) = updateAt-cong-local i (tail xs) eq j

updateAt-cong : ∀ (i : Fin n) {f g : A → A} → f ≗ g → (xs : Vector A n) →
                updateAt xs i f ≗ updateAt xs i g
updateAt-cong i eq xs = updateAt-cong-local i xs (eq (xs i))

-- The order of updates at different indices i ≢ j does not matter.

updateAt-commutes : ∀ (i j : Fin n) {f g : A → A} → i ≢ j → (xs : Vector A n) →
                    updateAt (updateAt xs j g) i f ≗ updateAt (updateAt xs i f) j g
updateAt-commutes zero    zero    0≢0 xs k       = ⊥-elim (0≢0 refl)
updateAt-commutes zero    (suc j) _   xs zero    = refl
updateAt-commutes zero    (suc j) _   xs (suc k) = refl
updateAt-commutes (suc i) zero    _   xs zero    = refl
updateAt-commutes (suc i) zero    _   xs (suc k) = refl
updateAt-commutes (suc i) (suc j) _   xs zero    = refl
updateAt-commutes (suc i) (suc j) i≢j xs (suc k) = updateAt-commutes i j (i≢j ∘ cong suc) (tail xs) k

------------------------------------------------------------------------
-- map

map-id : (xs : Vector A n) → map id xs ≗ xs
map-id xs = λ _ → refl

map-cong : ∀ {f g : A → B} → f ≗ g → (xs : Vector A n) → map f xs ≗ map g xs
map-cong f≗g xs = f≗g ∘ xs

map-∘ : ∀ {f : B → C} {g : A → B} (xs : Vector A n) →
        map (f ∘ g) xs ≗ map f (map g xs)
map-∘ xs = λ _ → refl

lookup-map : ∀ (i : Fin n) (f : A → B) (xs : Vector A n) →
             map f xs i ≡ f (xs i)
lookup-map i f xs = refl

map-updateAt-local : ∀ {f : A → B} {g : A → A} {h : B → B}
                     (xs : Vector A n) (i : Fin n) →
                     f (g (xs i)) ≡ h (f (xs i)) →
                     map f (updateAt xs i g) ≗ updateAt (map f xs) i h
map-updateAt-local {n = suc n}       {f = f} xs zero    eq zero    = eq
map-updateAt-local {n = suc n}       {f = f} xs zero    eq (suc j) = refl
map-updateAt-local {n = suc (suc n)} {f = f} xs (suc i) eq zero    = refl
map-updateAt-local {n = suc (suc n)} {f = f} xs (suc i) eq (suc j) = map-updateAt-local {f = f} (tail xs) i eq j

map-updateAt : ∀ {f : A → B} {g : A → A} {h : B → B} →
               f ∘ g ≗ h ∘ f →
               (xs : Vector A n) (i : Fin n) →
               map f (updateAt xs i g) ≗ updateAt (map f xs) i h
map-updateAt {f = f} {g = g} f∘g≗h∘f xs i = map-updateAt-local {f = f} {g = g} xs i (f∘g≗h∘f (xs i))

------------------------------------------------------------------------
-- _++_

lookup-++-< : ∀ (xs : Vector A m) (ys : Vector A n) →
              ∀ i (i<m : toℕ i ℕ.< m) →
              (xs ++ ys) i ≡ xs (fromℕ< i<m)
lookup-++-< {m = m} xs ys i i<m = cong Sum.[ xs , ys ] (Finₚ.splitAt-< m i i<m)

lookup-++-≥ : ∀ (xs : Vector A m) (ys : Vector A n) →
              ∀ i (i≥m : toℕ i ℕ.≥ m) →
              (xs ++ ys) i ≡ ys (reduce≥ i i≥m)
lookup-++-≥ {m = m} xs ys i i≥m = cong Sum.[ xs , ys ] (Finₚ.splitAt-≥ m i i≥m)

lookup-++ˡ : ∀ (xs : Vector A m) (ys : Vector A n) i →
             (xs ++ ys) (i ↑ˡ n) ≡ xs i
lookup-++ˡ {m = m} {n = n} xs ys i = cong Sum.[ xs , ys ] (Finₚ.splitAt-↑ˡ m i n)

lookup-++ʳ : ∀ (xs : Vector A m) (ys : Vector A n) i →
             (xs ++ ys) (m ↑ʳ i) ≡ ys i
lookup-++ʳ {m = m} {n = n} xs ys i = cong Sum.[ xs , ys ] (Finₚ.splitAt-↑ʳ m n i)

module _ {ys ys′ : Vector A m} where

  ++-cong : ∀ (xs xs′ : Vector A n) →
            xs ≗ xs′ → ys ≗ ys′ → xs ++ ys ≗ xs′ ++ ys′
  ++-cong {n} xs xs′ eq₁ eq₂ i with toℕ i ℕ.<? n
  ... | yes i<n = begin
    (xs ++ ys) i      ≡⟨ lookup-++-< xs ys i i<n ⟩
    xs (fromℕ< i<n)   ≡⟨ eq₁ (fromℕ< i<n) ⟩
    xs′ (fromℕ< i<n)  ≡⟨ lookup-++-< xs′ ys′ i i<n ⟨
    (xs′ ++ ys′) i    ∎
    where open ≡-Reasoning
  ... | no i≮n = begin
    (xs ++ ys) i               ≡⟨ lookup-++-≥ xs ys i (ℕ.≮⇒≥ i≮n) ⟩
    ys (reduce≥ i (ℕ.≮⇒≥ i≮n))   ≡⟨ eq₂ (reduce≥ i (ℕ.≮⇒≥ i≮n)) ⟩
    ys′ (reduce≥ i (ℕ.≮⇒≥ i≮n))  ≡⟨ lookup-++-≥ xs′ ys′ i (ℕ.≮⇒≥ i≮n) ⟨
    (xs′ ++ ys′) i             ∎
    where open ≡-Reasoning

  ++-injectiveˡ : ∀ (xs xs′ : Vector A n) →
                  xs ++ ys ≗ xs′ ++ ys′ → xs ≗ xs′
  ++-injectiveˡ xs xs′ eq i = begin
    xs i                   ≡⟨ lookup-++ˡ xs ys i ⟨
    (xs ++ ys) (i ↑ˡ m)    ≡⟨ eq (i ↑ˡ m) ⟩
    (xs′ ++ ys′) (i ↑ˡ m)  ≡⟨ lookup-++ˡ xs′ ys′ i ⟩
    xs′ i                  ∎
    where open ≡-Reasoning

  ++-injectiveʳ : ∀ (xs xs′ : Vector A n) → xs ++ ys ≗ xs′ ++ ys′ → ys ≗ ys′
  ++-injectiveʳ {n} xs xs′ eq i = begin
    ys i                   ≡⟨ lookup-++ʳ xs ys i ⟨
    (xs ++ ys) (n ↑ʳ i)    ≡⟨ eq (n ↑ʳ i)   ⟩
    (xs′ ++ ys′) (n ↑ʳ i)  ≡⟨ lookup-++ʳ xs′ ys′ i ⟩
    ys′ i                  ∎
    where open ≡-Reasoning

  ++-injective : ∀ (xs xs′ : Vector A n) →
                 xs ++ ys ≗ xs′ ++ ys′ → xs ≗ xs′ × ys ≗ ys′
  ++-injective xs xs′ eq = ++-injectiveˡ xs xs′ eq , ++-injectiveʳ xs xs′ eq

------------------------------------------------------------------------
-- insertAt

insertAt-lookup : ∀ (xs : Vector A n) (i : Fin (suc n)) (v : A) →
                  insertAt xs i v i ≡ v
insertAt-lookup {n = n}     xs zero    v = refl
insertAt-lookup {n = suc n} xs (suc i) v = insertAt-lookup (tail xs) i v

insertAt-punchIn : ∀ (xs : Vector A n) (i : Fin (suc n)) (v : A)
                   (j : Fin n) →
                   insertAt xs i v (punchIn i j) ≡ xs j
insertAt-punchIn {n = suc n} xs zero    v j       = refl
insertAt-punchIn {n = suc n} xs (suc i) v zero    = refl
insertAt-punchIn {n = suc n} xs (suc i) v (suc j) = insertAt-punchIn (tail xs) i v j

------------------------------------------------------------------------
-- removeAt

removeAt-punchOut : ∀ (xs : Vector A (suc n))
                  {i : Fin (suc n)} {j : Fin (suc n)} (i≢j : i ≢ j) →
                  removeAt xs i (punchOut i≢j) ≡ xs j
removeAt-punchOut {n = n}     xs {zero}  {zero}  i≢j = ⊥-elim (i≢j refl)
removeAt-punchOut {n = suc n} xs {zero}  {suc j} i≢j = refl
removeAt-punchOut {n = suc n} xs {suc i} {zero}  i≢j = refl
removeAt-punchOut {n = suc n} xs {suc i} {suc j} i≢j = removeAt-punchOut (tail xs) (i≢j ∘ cong suc)

removeAt-insertAt : ∀ (xs : Vector A n) (i : Fin (suc n)) (v : A) →
                    removeAt (insertAt xs i v) i ≗ xs
removeAt-insertAt xs zero    v j       = refl
removeAt-insertAt xs (suc i) v zero    = refl
removeAt-insertAt xs (suc i) v (suc j) = removeAt-insertAt (tail xs) i v j

insertAt-removeAt : ∀ (xs : Vector A (suc n)) (i : Fin (suc n)) →
                    insertAt (removeAt xs i) i (xs i) ≗ xs
insertAt-removeAt {n = n}     xs zero    zero    = refl
insertAt-removeAt {n = n}     xs zero    (suc j) = refl
insertAt-removeAt {n = suc n} xs (suc i) zero    = refl
insertAt-removeAt {n = suc n} xs (suc i) (suc j) = insertAt-removeAt (tail xs) i j

------------------------------------------------------------------------
-- Conversion functions

toVec∘fromVec : (xs : Vec A n) → toVec (fromVec xs) ≡ xs
toVec∘fromVec = Vec.tabulate∘lookup

fromVec∘toVec : (xs : Vector A n) → fromVec (toVec xs) ≗ xs
fromVec∘toVec = Vec.lookup∘tabulate

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList = List.tabulate-lookup

------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

updateAt-id-relative = updateAt-id-local
{-# WARNING_ON_USAGE updateAt-id-relative
"Warning: updateAt-id-relative was deprecated in v2.0.
Please use updateAt-id-local instead."
#-}
updateAt-compose-relative = updateAt-updateAt-local
{-# WARNING_ON_USAGE updateAt-compose-relative
"Warning: updateAt-compose-relative was deprecated in v2.0.
Please use updateAt-updateAt-local instead."
#-}
updateAt-compose = updateAt-updateAt
{-# WARNING_ON_USAGE updateAt-compose
"Warning: updateAt-compose was deprecated in v2.0.
Please use updateAt-updateAt instead."
#-}
updateAt-cong-relative = updateAt-cong-local
{-# WARNING_ON_USAGE updateAt-cong-relative
"Warning: updateAt-cong-relative was deprecated in v2.0.
Please use updateAt-cong-local instead."
#-}

insert-lookup = insertAt-lookup
{-# WARNING_ON_USAGE insert-lookup
"Warning: insert-lookup was deprecated in v2.0.
Please use insertAt-lookup instead."
#-}
insert-punchIn = insertAt-punchIn
{-# WARNING_ON_USAGE insert-punchIn
"Warning: insert-punchIn was deprecated in v2.0.
Please use insertAt-punchIn instead."
#-}
remove-punchOut = removeAt-punchOut
{-# WARNING_ON_USAGE remove-punchOut
"Warning: remove-punchOut was deprecated in v2.0.
Please use removeAt-punchOut instead."
#-}
remove-insert = removeAt-insertAt
{-# WARNING_ON_USAGE remove-insert
"Warning: remove-insert was deprecated in v2.0.
Please use removeAt-insertAt instead."
#-}
insert-remove = insertAt-removeAt
{-# WARNING_ON_USAGE insert-remove
"Warning: insert-remove was deprecated in v2.0.
Please use insertAt-removeAt instead."
#-}
