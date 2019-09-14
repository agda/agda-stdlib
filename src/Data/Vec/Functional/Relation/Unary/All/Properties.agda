------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Unary.All.Properties where

open import Data.Fin
open import Data.Fin.Properties
open import Data.Nat
open import Data.Product as Σ using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Functional as VF hiding (map)
open import Data.Vec.Functional.Relation.Unary.All
open import Function
open import Level using (Level)
open import Relation.Unary

private
  variable
    a b c p q r ℓ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- map

map⁺ : {P : Pred A p} {Q : Pred B q} {f : A → B} →
       (∀ {x} → P x → Q (f x)) → ∀ {n} →
       (∀ {xs} → All P {n = n} xs → All Q (VF.map f xs))
map⁺ pq ps i = pq (ps i)

------------------------------------------------------------------------
-- replicate

replicate⁺ : ∀ {P : Pred A p} {x n} → P x → All P (replicate {n = n} x)
replicate⁺ = const

------------------------------------------------------------------------
-- _⊛_

⊛⁺ : ∀ {P : Pred A p} {Q : Pred B q} {n} {fs : Vector (A → B) n} {xs} →
     All (λ f → ∀ {x} → P x → Q (f x)) fs → All P xs → All Q (fs ⊛ xs)
⊛⁺ pqs ps i = (pqs i) (ps i)

------------------------------------------------------------------------
-- zipWith

zipWith⁺ : ∀ {P : Pred A p} {Q : Pred B q} {R : Pred C r} {n xs ys f} →
           (∀ {x y} → P x → Q y → R (f x y)) →
           All P xs → All Q ys → All R (zipWith f {n = n} xs ys)
zipWith⁺ pqr ps qs i = pqr (ps i) (qs i)

------------------------------------------------------------------------
-- zip

zip⁺ : ∀ {P : Pred A p} {Q : Pred B q} {n xs ys} →
       All P xs → All Q ys → All (uncurry _×_ ∘ Σ.map P Q) (zip {n = n} xs ys)
zip⁺ ps qs i = ps i , qs i

zip⁻ : ∀ {P : Pred A p} {Q : Pred B q} {n xs ys} →
       All (uncurry _×_ ∘ Σ.map P Q) (zip {n = n} xs ys) → All P xs × All Q ys
zip⁻ pqs = proj₁ ∘ pqs , proj₂ ∘ pqs

------------------------------------------------------------------------
-- head

head⁺ : ∀ (P : Pred A p) {n v} → All P v → P (head {n = n} v)
head⁺ P ps = ps zero

------------------------------------------------------------------------
-- tail

tail⁺ : ∀ (P : Pred A p) {n v} → All P v → All P (tail {n = n} v)
tail⁺ P ps = ps ∘ suc

------------------------------------------------------------------------
-- ++

++⁺ : ∀ (P : Pred A p) {m n xs ys} →
      All P {n = m} xs → All P {n = n} ys → All P (xs ++ ys)
++⁺ P {m} {n} pxs pys i with split+ m i
... | inj₁ i′ = pxs i′
... | inj₂ j′ = pys j′

++⁻ˡ : ∀ (P : Pred A p) {m n} (xs : Vector A m) {ys : Vector A n} →
       All P (xs ++ ys) → All P xs
++⁻ˡ P {m} {n} _ ps i with ps (inject+ n i)
... | p rewrite split+-inject+ m n i = p

++⁻ʳ : ∀ (P : Pred A p) {m n} (xs : Vector A m) {ys : Vector A n} →
       All P (xs ++ ys) → All P ys
++⁻ʳ P {m} {n} _ ps i with ps (raise m i)
... | p rewrite split+-raise m n i = p

++⁻ : ∀ (P : Pred A p) {m n} (xs : Vector A m) {ys : Vector A n} →
      All P (xs ++ ys) → All P xs × All P ys
++⁻ P _ ps = ++⁻ˡ P _ ps , ++⁻ʳ P _ ps
