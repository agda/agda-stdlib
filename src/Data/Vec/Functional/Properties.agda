------------------------------------------------------------------------
-- The Agda standard library
--
-- Some Vector-related properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Vec.Functional.Properties where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕₚ
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Base as L using (List)
import Data.List.Properties as Lₚ
open import Data.Sum.Base as Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec as V using (Vec)
import Data.Vec.Properties as Vₚ
open import Data.Vec.Functional
open import Function.Base
open import Level using (Level)
open import Relation.Binary as B
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
  using (Dec; does; yes; no; map′; _×-dec_)

import Data.Fin.Properties as Finₚ

private
  variable
    a b c : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------

module _ {n} {xs ys : Vector A (suc n)} where

  ∷-cong : head xs ≡ head ys → tail xs ≗ tail ys → xs ≗ ys
  ∷-cong eq _ zero    = eq
  ∷-cong _ eq (suc i) = eq i

  ∷-injective : xs ≗ ys → head xs ≡ head ys × tail xs ≗ tail ys
  ∷-injective eq = eq zero , eq ∘ suc

≗-dec : B.DecidableEquality A →
        ∀ {n} → B.Decidable {A = Vector A n} _≗_
≗-dec _≟_ {zero}  xs ys = yes λ ()
≗-dec _≟_ {suc n} xs ys =
  map′ (Product.uncurry ∷-cong) ∷-injective
       (head xs ≟ head ys ×-dec ≗-dec _≟_ (tail xs) (tail ys))

------------------------------------------------------------------------
-- updateAt

-- (+) updateAt i actually updates the element at index i.

updateAt-updates : ∀ {n} (i : Fin n) {f : A → A} (xs : Vector A n) →
                   updateAt i f xs i ≡ f (xs i)
updateAt-updates zero    xs = refl
updateAt-updates (suc i) xs = updateAt-updates i (tail xs)

-- (-) updateAt i does not touch the elements at other indices.

updateAt-minimal : ∀ {n} (i j : Fin n) {f : A → A} (xs : Vector A n) →
                   i ≢ j → updateAt j f xs i ≡ xs i
updateAt-minimal zero    zero    xs 0≢0 = ⊥-elim (0≢0 refl)
updateAt-minimal zero    (suc j) xs _   = refl
updateAt-minimal (suc i) zero    xs _   = refl
updateAt-minimal (suc i) (suc j) xs i≢j = updateAt-minimal i j (tail xs) (i≢j ∘ cong suc)

-- updateAt i is a monoid morphism from A → A to Vector A n → Vector A n.

updateAt-id-local : ∀ {n} (i : Fin n) {f : A → A} (xs : Vector A n) →
                    f (xs i) ≡ xs i →
                    updateAt i f xs ≗ xs
updateAt-id-local zero    xs eq zero    = eq
updateAt-id-local zero    xs eq (suc j) = refl
updateAt-id-local (suc i) xs eq zero    = refl
updateAt-id-local (suc i) xs eq (suc j) = updateAt-id-local i (tail xs) eq j

updateAt-id : ∀ {n} (i : Fin n) (xs : Vector A n) →
              updateAt i id xs ≗ xs
updateAt-id i xs = updateAt-id-local i xs refl

updateAt-∘-local : ∀ {n} (i : Fin n) {f g h : A → A} (xs : Vector A n) →
                   f (g (xs i)) ≡ h (xs i) →
                   updateAt i f (updateAt i g xs) ≗ updateAt i h xs
updateAt-∘-local zero    xs eq zero    = eq
updateAt-∘-local zero    xs eq (suc j) = refl
updateAt-∘-local (suc i) xs eq zero    = refl
updateAt-∘-local (suc i) xs eq (suc j) = updateAt-∘-local i (tail xs) eq j

updateAt-∘ : ∀ {n} (i : Fin n) {f g : A → A} (xs : Vector A n) →
             updateAt i f (updateAt i g xs) ≗ updateAt i (f ∘ g) xs
updateAt-∘ i xs = updateAt-∘-local i xs refl

updateAt-cong-local : ∀ {n} (i : Fin n) {f g : A → A} (xs : Vector A n) →
                      f (xs i) ≡ g (xs i) →
                      updateAt i f xs ≗ updateAt i g xs
updateAt-cong-local zero    xs eq zero    = eq
updateAt-cong-local zero    xs eq (suc j) = refl
updateAt-cong-local (suc i) xs eq zero    = refl
updateAt-cong-local (suc i) xs eq (suc j) = updateAt-cong-local i (tail xs) eq j

updateAt-cong : ∀ {n} (i : Fin n) {f g : A → A} →
                f ≗ g → (xs : Vector A n) → updateAt i f xs ≗ updateAt i g xs
updateAt-cong i eq xs = updateAt-cong-local i xs (eq (xs i))

-- The order of updates at different indices i ≢ j does not matter.

updateAt-commutes : ∀ {n} (i j : Fin n) {f g : A → A} → i ≢ j → (xs : Vector A n) →
                    updateAt i f (updateAt j g xs) ≗ updateAt j g (updateAt i f xs)
updateAt-commutes zero    zero    0≢0 xs k       = ⊥-elim (0≢0 refl)
updateAt-commutes zero    (suc j) _   xs zero    = refl
updateAt-commutes zero    (suc j) _   xs (suc k) = refl
updateAt-commutes (suc i) zero    _   xs zero    = refl
updateAt-commutes (suc i) zero    _   xs (suc k) = refl
updateAt-commutes (suc i) (suc j) _   xs zero    = refl
updateAt-commutes (suc i) (suc j) i≢j xs (suc k) = updateAt-commutes i j (i≢j ∘ cong suc) (tail xs) k

------------------------------------------------------------------------
-- map

map-id : ∀ {n} → (xs : Vector A n) → map id xs ≗ xs
map-id xs = λ _ → refl

map-cong : ∀ {n} {f g : A → B} → f ≗ g → (xs : Vector A n) → map f xs ≗ map g xs
map-cong f≗g xs = f≗g ∘ xs

map-∘ : ∀ {n} {f : B → C} {g : A → B} →
        (xs : Vector A n) → map (f ∘ g) xs ≗ map f (map g xs)
map-∘ xs = λ _ → refl

lookup-map : ∀ {n} (i : Fin n) (f : A → B) (xs : Vector A n) →
             map f xs i ≡ f (xs i)
lookup-map i f xs = refl

map-updateAt-local : ∀ {n} {f : A → B} {g : A → A} {h : B → B}
                     (xs : Vector A n) (i : Fin n) →
                     f (g (xs i)) ≡ h (f (xs i)) →
                     map f (updateAt i g xs) ≗ updateAt i h (map f xs)
map-updateAt-local {n = suc n}       {f = f} xs zero    eq zero    = eq
map-updateAt-local {n = suc n}       {f = f} xs zero    eq (suc j) = refl
map-updateAt-local {n = suc (suc n)} {f = f} xs (suc i) eq zero    = refl
map-updateAt-local {n = suc (suc n)} {f = f} xs (suc i) eq (suc j) = map-updateAt-local {f = f} (tail xs) i eq j

map-updateAt : ∀ {n} {f : A → B} {g : A → A} {h : B → B} →
               f ∘ g ≗ h ∘ f →
               (xs : Vector A n) (i : Fin n) →
               map f (updateAt i g xs) ≗ updateAt i h (map f xs)
map-updateAt {f = f} {g = g} f∘g≗h∘f xs i = map-updateAt-local {f = f} {g = g} xs i (f∘g≗h∘f (xs i))

------------------------------------------------------------------------
-- _++_

lookup-++-< : ∀ {m n} (xs : Vector A m) (ys : Vector A n) →
              ∀ i (i<m : toℕ i ℕ.< m) →
              (xs ++ ys) i ≡ xs (fromℕ< i<m)
lookup-++-< {m = m} xs ys i i<m = cong Sum.[ xs , ys ] (Finₚ.splitAt-< m i i<m)

lookup-++-≥ : ∀ {m n} (xs : Vector A m) (ys : Vector A n) →
              ∀ i (i≥m : toℕ i ℕ.≥ m) →
              (xs ++ ys) i ≡ ys (reduce≥ i i≥m)
lookup-++-≥ {m = m} xs ys i i≥m = cong Sum.[ xs , ys ] (Finₚ.splitAt-≥ m i i≥m)

lookup-++ˡ : ∀ {m n} (xs : Vector A m) (ys : Vector A n) i →
             (xs ++ ys) (i ↑ˡ n) ≡ xs i
lookup-++ˡ {m = m} {n = n} xs ys i = cong Sum.[ xs , ys ] (Finₚ.splitAt-↑ˡ m i n)

lookup-++ʳ : ∀ {m n} (xs : Vector A m) (ys : Vector A n) i →
             (xs ++ ys) (m ↑ʳ i) ≡ ys i
lookup-++ʳ {m = m} {n = n} xs ys i = cong Sum.[ xs , ys ] (Finₚ.splitAt-↑ʳ m n i)

module _ {m} {ys ys′ : Vector A m} where

  ++-cong : ∀ {n} (xs xs′ : Vector A n) →
            xs ≗ xs′ → ys ≗ ys′ → xs ++ ys ≗ xs′ ++ ys′
  ++-cong {n} xs xs′ eq₁ eq₂ i with toℕ i ℕₚ.<? n
  ... | yes i<n = begin
    (xs ++ ys) i      ≡⟨ lookup-++-< xs ys i i<n ⟩
    xs (fromℕ< i<n)   ≡⟨ eq₁ (fromℕ< i<n) ⟩
    xs′ (fromℕ< i<n)  ≡˘⟨ lookup-++-< xs′ ys′ i i<n ⟩
    (xs′ ++ ys′) i    ∎
    where open ≡-Reasoning
  ... | no i≮n = begin
    (xs ++ ys) i               ≡⟨ lookup-++-≥ xs ys i (ℕₚ.≮⇒≥ i≮n) ⟩
    ys (reduce≥ i (ℕₚ.≮⇒≥ i≮n))   ≡⟨ eq₂ (reduce≥ i (ℕₚ.≮⇒≥ i≮n)) ⟩
    ys′ (reduce≥ i (ℕₚ.≮⇒≥ i≮n))  ≡˘⟨ lookup-++-≥ xs′ ys′ i (ℕₚ.≮⇒≥ i≮n) ⟩
    (xs′ ++ ys′) i             ∎
    where open ≡-Reasoning

  ++-injectiveˡ : ∀ {n} (xs xs′ : Vector A n) →
                  xs ++ ys ≗ xs′ ++ ys′ → xs ≗ xs′
  ++-injectiveˡ xs xs′ eq i = begin
    xs i                   ≡˘⟨ lookup-++ˡ xs ys i ⟩
    (xs ++ ys) (i ↑ˡ m)    ≡⟨ eq (i ↑ˡ m) ⟩
    (xs′ ++ ys′) (i ↑ˡ m)  ≡⟨ lookup-++ˡ xs′ ys′ i ⟩
    xs′ i                  ∎
    where open ≡-Reasoning

  ++-injectiveʳ : ∀ {n} (xs xs′ : Vector A n) →
                  xs ++ ys ≗ xs′ ++ ys′ → ys ≗ ys′
  ++-injectiveʳ {n} xs xs′ eq i = begin
    ys i                   ≡˘⟨ lookup-++ʳ xs ys i ⟩
    (xs ++ ys) (n ↑ʳ i)    ≡⟨ eq (n ↑ʳ i)   ⟩
    (xs′ ++ ys′) (n ↑ʳ i)  ≡⟨ lookup-++ʳ xs′ ys′ i ⟩
    ys′ i                  ∎
    where open ≡-Reasoning

  ++-injective : ∀ {n} (xs xs′ : Vector A n) →
                 xs ++ ys ≗ xs′ ++ ys′ → xs ≗ xs′ × ys ≗ ys′
  ++-injective xs xs′ eq = ++-injectiveˡ xs xs′ eq , ++-injectiveʳ xs xs′ eq

------------------------------------------------------------------------
-- insert

insert-lookup : ∀ {n} (xs : Vector A n) (i : Fin (suc n)) (v : A) →
                insert xs i v i ≡ v
insert-lookup {n = n}     xs zero    v = refl
insert-lookup {n = suc n} xs (suc i) v = insert-lookup (tail xs) i v

insert-punchIn : ∀ {n} (xs : Vector A n) (i : Fin (suc n)) (v : A)
                 (j : Fin n) →
                 insert xs i v (punchIn i j) ≡ xs j
insert-punchIn {n = suc n} xs zero    v j       = refl
insert-punchIn {n = suc n} xs (suc i) v zero    = refl
insert-punchIn {n = suc n} xs (suc i) v (suc j) = insert-punchIn (tail xs) i v j

------------------------------------------------------------------------
-- remove

remove-punchOut : ∀ {n} (xs : Vector A (suc n))
                  {i : Fin (suc n)} {j : Fin (suc n)} (i≢j : i ≢ j) →
                  remove i xs (punchOut i≢j) ≡ xs j
remove-punchOut {n = n}     xs {zero}  {zero}  i≢j = ⊥-elim (i≢j refl)
remove-punchOut {n = suc n} xs {zero}  {suc j} i≢j = refl
remove-punchOut {n = suc n} xs {suc i} {zero}  i≢j = refl
remove-punchOut {n = suc n} xs {suc i} {suc j} i≢j = remove-punchOut (tail xs) (i≢j ∘ cong suc)

remove-insert : ∀ {n} (xs : Vector A n) (i : Fin (suc n)) (v : A) →
                remove i (insert xs i v) ≗ xs
remove-insert xs zero    v j       = refl
remove-insert xs (suc i) v zero    = refl
remove-insert xs (suc i) v (suc j) = remove-insert (tail xs) i v j

insert-remove : ∀ {n} (xs : Vector A (suc n)) (i : Fin (suc n)) →
                insert (remove i xs) i (xs i) ≗ xs
insert-remove {n = n}     xs zero    zero    = refl
insert-remove {n = n}     xs zero    (suc j) = refl
insert-remove {n = suc n} xs (suc i) zero    = refl
insert-remove {n = suc n} xs (suc i) (suc j) = insert-remove (tail xs) i j

------------------------------------------------------------------------
-- Conversion functions

toVec∘fromVec : ∀ {n} → (xs : Vec A n) → toVec (fromVec xs) ≡ xs
toVec∘fromVec = Vₚ.tabulate∘lookup

fromVec∘toVec : ∀ {n} → (xs : Vector A n) → fromVec (toVec xs) ≗ xs
fromVec∘toVec = Vₚ.lookup∘tabulate

toList∘fromList : (xs : List A) → toList (fromList xs) ≡ xs
toList∘fromList = Lₚ.tabulate-lookup

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

updateAt-compose-relative = updateAt-∘-local
{-# WARNING_ON_USAGE updateAt-compose-relative
"Warning: updateAt-compose-relative was deprecated in v2.0.
Please use updateAt-∘-local instead."
#-}

updateAt-compose = updateAt-∘
{-# WARNING_ON_USAGE updateAt-compose
"Warning: updateAt-compose was deprecated in v2.0.
Please use updateAt-∘ instead."
#-}

updateAt-cong-relative = updateAt-cong-local
{-# WARNING_ON_USAGE updateAt-cong-relative
"Warning: updateAt-cong-relative was deprecated in v2.0.
Please use updateAt-cong-local instead."
#-}
