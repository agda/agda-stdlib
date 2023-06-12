------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary vectors
------------------------------------------------------------------------

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Vec.Binary.Properties where

open import Data.Fin.Binary.Base
open import Data.Nat.Binary.Base
open import Data.Vec.Binary.Base
open import Function.Base
open import Level using (Level)
open import Relation.Binary.PropositionalEquality

private
  variable
    a b c d : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d
    n : ℕᵇ

-- Properties of head, tail, and _∷_
------------------------------------------------------------------------

head-∷ : ∀ x (xs : Vecᵇ A n) → head (x ∷ xs) ≡ x
head-∷ x [] = refl
head-∷ x (_ ∷⟨ _ / _ ⟩) = refl
head-∷ x (_ × _ ∷⟨ _ / _ ⟩) = refl

merge-∷ : ∀ x₁ x₂ (xs₁ xs₂ : Vecᵇ A n) → merge (x₁ ∷ xs₁) (x₂ ∷ xs₂) ≡ x₁ × x₂ ∷⟨ xs₁ / xs₂ ⟩
merge-∷ x₁ x₂ [] [] = refl
merge-∷ x₁ x₂ (x ∷⟨ xs₁ / xs₂ ⟩) (x₃ ∷⟨ xs₃ / xs₄ ⟩) = refl
merge-∷ x₁ x₂ (y₁ × z₁ ∷⟨ ls₁ / rs₁ ⟩) (y₂ × z₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ (x₁ × x₂ ∷⟨_/_⟩) (merge-∷ y₁ z₁ ls₁ rs₁) (merge-∷ y₂ z₂ ls₂ rs₂)

tail-∷ : ∀ x (xs : Vecᵇ A n) → tail (x ∷ xs) ≡ xs
tail-∷ x [] = refl
tail-∷ x (y ∷⟨ ls / rs ⟩) = refl
tail-∷ x (y × z ∷⟨ ls / rs ⟩) = merge-∷ y z ls rs

∷-merge : ∀ x (ls rs : Vecᵇ A (suc n)) → x ∷ merge ls rs ≡ x ∷⟨ ls / rs ⟩
∷-merge {n = zero} x (y₁ ∷⟨ [] / [] ⟩) (y₂ ∷⟨ [] / [] ⟩) = refl
∷-merge {n = 2[1+ n ]} x (y₁ ∷⟨ ls₁ / rs₁ ⟩) (y₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ (x ∷⟨_/_⟩) (∷-merge y₁ ls₁ rs₁) (∷-merge y₂ ls₂ rs₂)
∷-merge {n = 1+[2 n ]} x (y₁ × z₁ ∷⟨ ls₁ / rs₁ ⟩) (y₂ × z₂ ∷⟨ ls₂ / rs₂ ⟩) = refl

∷-head-tail : ∀ (xs : Vecᵇ A (suc n)) → head xs ∷ tail xs ≡ xs
∷-head-tail {n = zero} (x ∷⟨ [] / [] ⟩) = refl
∷-head-tail {n = 2[1+ n ]} (x ∷⟨ ls / rs ⟩) = ∷-merge x ls rs
∷-head-tail {n = 1+[2 n ]} (x × y ∷⟨ ls / rs ⟩) = refl

-- Properties of replicate, map, and zipWith
------------------------------------------------------------------------

lookup-replicate : ∀ (i : Finᵇ n) (x : A) → lookup (replicate x) i ≡ x
lookup-replicate zeroᵒ x = refl
lookup-replicate zeroᵉ x = refl
lookup-replicate oneᵉ x = refl
lookup-replicate 1+[2 i ]ᵒ x = lookup-replicate i x
lookup-replicate 2[1+ i ]ᵒ x = lookup-replicate i x
lookup-replicate 2[1+ i ]ᵉ x = lookup-replicate i x
lookup-replicate 3+[2 i ]ᵉ x = lookup-replicate i x

map-replicate : (f : A → B) (x : A) → map f (replicate {n = n} x) ≡ replicate (f x)
map-replicate {n = zero} f x = refl
map-replicate {n = 2[1+ n ]} f x = cong₂ (f x × f x ∷⟨_/_⟩) (map-replicate f x) (map-replicate f x)
map-replicate {n = 1+[2 n ]} f x = cong₂ (f x ∷⟨_/_⟩) (map-replicate f x) (map-replicate f x)

lookup-map : ∀ (i : Finᵇ n) (f : A → B) (xs : Vecᵇ A n) → lookup (map f xs) i ≡ f (lookup xs i)
lookup-map zeroᵒ f (x ∷⟨ ls / rs ⟩) = refl
lookup-map zeroᵉ f (x × y ∷⟨ ls / rs ⟩) = refl
lookup-map oneᵉ f (x × y ∷⟨ ls / rs ⟩) = refl
lookup-map 1+[2 i ]ᵒ f (x ∷⟨ ls / rs ⟩) = lookup-map i f ls
lookup-map 2[1+ i ]ᵒ f (x ∷⟨ ls / rs ⟩) = lookup-map i f rs
lookup-map 2[1+ i ]ᵉ f (x × y ∷⟨ ls / rs ⟩) = lookup-map i f ls
lookup-map 3+[2 i ]ᵉ f (x × y ∷⟨ ls / rs ⟩) = lookup-map i f rs

map-id : (xs : Vecᵇ A n) → map id xs ≡ xs
map-id [] = refl
map-id (x ∷⟨ ls / rs ⟩) = cong₂ (x ∷⟨_/_⟩) (map-id ls) (map-id rs)
map-id (x × y ∷⟨ ls / rs ⟩) = cong₂ (x × y ∷⟨_/_⟩) (map-id ls) (map-id rs)

map-const : (x : B) (xs : Vecᵇ A n) → map (const x) xs ≡ replicate x
map-const x [] = refl
map-const x (y ∷⟨ ls / rs ⟩) = cong₂ (x ∷⟨_/_⟩) (map-const x ls) (map-const x rs)
map-const x (y × z ∷⟨ ls / rs ⟩) = cong₂ (x × x ∷⟨_/_⟩) (map-const x ls) (map-const x rs)

map-∘ : (f : B → C) (g : A → B) → map {n = n} (f ∘ g) ≗ map f ∘ map g
map-∘ f g [] = refl
map-∘ f g (x ∷⟨ ls / rs ⟩) = cong₂ (f (g x) ∷⟨_/_⟩) (map-∘ f g ls) (map-∘ f g rs)
map-∘ f g (x × y ∷⟨ ls / rs ⟩) = cong₂ (f (g x) × f (g y) ∷⟨_/_⟩) (map-∘ f g ls) (map-∘ f g rs)

zipWith-lookup : (i : Finᵇ n) (f : A → B → C) (xs : Vecᵇ A n) (ys : Vecᵇ B n) → lookup (zipWith f xs ys) i ≡ f (lookup xs i) (lookup ys i)
zipWith-lookup zeroᵒ f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = refl
zipWith-lookup zeroᵉ f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = refl
zipWith-lookup oneᵉ f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = refl
zipWith-lookup 1+[2 i ]ᵒ f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = zipWith-lookup i f ls₁ ls₂
zipWith-lookup 2[1+ i ]ᵒ f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = zipWith-lookup i f rs₁ rs₂
zipWith-lookup 2[1+ i ]ᵉ f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = zipWith-lookup i f ls₁ ls₂
zipWith-lookup 3+[2 i ]ᵉ f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = zipWith-lookup i f rs₁ rs₂

zipWith-map₁ : (_⊕_ : B → C → D) (f : A → B) (xs : Vecᵇ A n) (ys : Vecᵇ C n) → zipWith _⊕_ (map f xs) ys ≡ zipWith (f -⟨ _⊕_ ∣) xs ys
zipWith-map₁ _⊕_ f [] [] = refl
zipWith-map₁ _⊕_ f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ ((f x₁ ⊕ x₂) ∷⟨_/_⟩) (zipWith-map₁ _⊕_ f ls₁ ls₂) (zipWith-map₁ _⊕_ f rs₁ rs₂)
zipWith-map₁ _⊕_ f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ ((f x₁ ⊕ x₂) × f y₁ ⊕ y₂ ∷⟨_/_⟩) (zipWith-map₁ _⊕_ f ls₁ ls₂) (zipWith-map₁ _⊕_ f rs₁ rs₂)

zipWith-map₂ : (_⊕_ : A → C → D) (f : B → C) (xs : Vecᵇ A n) (ys : Vecᵇ B n) → zipWith _⊕_ xs (map f ys) ≡ zipWith (∣ _⊕_ ⟩- f) xs ys
zipWith-map₂ _⊕_ f [] [] = refl
zipWith-map₂ _⊕_ f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ ((x₁ ⊕ f x₂) ∷⟨_/_⟩) (zipWith-map₂ _⊕_ f ls₁ ls₂) (zipWith-map₂ _⊕_ f rs₁ rs₂)
zipWith-map₂ _⊕_ f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ ((x₁ ⊕ f x₂) × y₁ ⊕ f y₂ ∷⟨_/_⟩) (zipWith-map₂ _⊕_ f ls₁ ls₂) (zipWith-map₂ _⊕_ f rs₁ rs₂)

-- Properties relating head, tail, and _∷_ to replicate, map, and zipWith
------------------------------------------------------------------------

head-replicate : (x : A) → head (replicate {n = suc n} x) ≡ x
head-replicate {n = zero} x = refl
head-replicate {n = 2[1+ n ]} x = refl
head-replicate {n = 1+[2 n ]} x = refl

merge-replicate : (x : A) → merge (replicate {n = suc n} x) (replicate x) ≡ x × x ∷⟨ replicate x / replicate x ⟩
merge-replicate {n = zero} x = refl
merge-replicate {n = 2[1+ n ]} x = cong₂ (x × x ∷⟨_/_⟩) (merge-replicate x) (merge-replicate x)
merge-replicate {n = 1+[2 n ]} x = refl

tail-replicate : (x : A) → tail (replicate {n = suc n} x) ≡ replicate x
tail-replicate {n = zero} x = refl
tail-replicate {n = 2[1+ n ]} x = merge-replicate x
tail-replicate {n = 1+[2 n ]} x = refl

∷-replicate : (x : A) → x ∷ replicate {n = n} x ≡ replicate x
∷-replicate {n = zero} x = refl
∷-replicate {n = 2[1+ n ]} x = cong₂ (x ∷⟨_/_⟩) (∷-replicate x) (∷-replicate x)
∷-replicate {n = 1+[2 n ]} x = refl

head-map : (f : A → B) (xs : Vecᵇ A (suc n)) → head (map f xs) ≡ f (head xs)
head-map {n = zero} f (x ∷⟨ [] / [] ⟩) = refl
head-map {n = 2[1+ n ]} f (x ∷⟨ ls / rs ⟩) = refl
head-map {n = 1+[2 n ]} f (x × y ∷⟨ ls / rs ⟩) = refl

merge-map : (f : A → B) (ls rs : Vecᵇ A (suc n)) → merge (map f ls) (map f rs) ≡ map f (merge ls rs)
merge-map {n = zero} f (x₁ ∷⟨ [] / [] ⟩) (x₂ ∷⟨ [] / [] ⟩) = refl
merge-map {n = 2[1+ n ]} f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = cong₂ (f x₁ × f x₂ ∷⟨_/_⟩) (merge-map f ls₁ rs₁) (merge-map f ls₂ rs₂)
merge-map {n = 1+[2 n ]} f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = refl

tail-map : (f : A → B) (xs : Vecᵇ A (suc n)) → tail (map f xs) ≡ map f (tail xs)
tail-map {n = zero} f (x ∷⟨ [] / [] ⟩) = refl
tail-map {n = 2[1+ n ]} f (x ∷⟨ ls / rs ⟩) = merge-map f ls rs
tail-map {n = 1+[2 n ]} f (x × y ∷⟨ ls / rs ⟩) = refl

head-zipWith : (f : A → B → C) (xs : Vecᵇ A (suc n)) (ys : Vecᵇ B (suc n)) → head (zipWith f xs ys) ≡ f (head xs) (head ys)
head-zipWith {n = zero} f (x₁ ∷⟨ [] / [] ⟩) (x₂ ∷⟨ [] / [] ⟩) = refl
head-zipWith {n = 2[1+ n ]} f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = refl
head-zipWith {n = 1+[2 n ]} f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = refl

merge-zipWith : (f : A → B → C) (ls₁ rs₁ : Vecᵇ A (suc n)) (ls₂ rs₂ : Vecᵇ B (suc n)) → merge (zipWith f ls₁ ls₂) (zipWith f rs₁ rs₂) ≡ zipWith f (merge ls₁ rs₁) (merge ls₂ rs₂)
merge-zipWith {n = zero} f (lx₁ ∷⟨ [] / [] ⟩) (rx₁ ∷⟨ [] / [] ⟩) (lx₂ ∷⟨ [] / [] ⟩) (rx₂ ∷⟨ [] / [] ⟩) = refl
merge-zipWith {n = 2[1+ n ]} f (lx₁ ∷⟨ lls₁ / lrs₁ ⟩) (rx₁ ∷⟨ rls₁ / rrs₁ ⟩) (lx₂ ∷⟨ lls₂ / lrs₂ ⟩) (rx₂ ∷⟨ rls₂ / rrs₂ ⟩) = cong₂ (f lx₁ lx₂ × f rx₁ rx₂ ∷⟨_/_⟩) (merge-zipWith f lls₁ lrs₁ lls₂ lrs₂) (merge-zipWith f rls₁ rrs₁ rls₂ rrs₂)
merge-zipWith {n = 1+[2 n ]} f (lx₁ × ly₁ ∷⟨ lls₁ / lrs₁ ⟩) (rx₁ × ry₁ ∷⟨ rls₁ / rrs₁ ⟩) (lx₂ × ly₂ ∷⟨ lls₂ / lrs₂ ⟩) (rx₂ × ry₂ ∷⟨ rls₂ / rrs₂ ⟩) = refl

tail-zipWith : (f : A → B → C) (xs : Vecᵇ A (suc n)) (ys : Vecᵇ B (suc n)) → tail (zipWith f xs ys) ≡ zipWith f (tail xs) (tail ys)
tail-zipWith {n = zero} f (x₁ ∷⟨ [] / [] ⟩) (x₂ ∷⟨ [] / [] ⟩) = refl
tail-zipWith {n = 2[1+ n ]} f (x₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ ∷⟨ ls₂ / rs₂ ⟩) = merge-zipWith f ls₁ rs₁ ls₂ rs₂
tail-zipWith {n = 1+[2 n ]} f (x₁ × y₁ ∷⟨ ls₁ / rs₁ ⟩) (x₂ × y₂ ∷⟨ ls₂ / rs₂ ⟩) = refl
