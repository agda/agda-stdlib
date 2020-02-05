------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Unary.All.Properties where

open import Data.Fin.Base
open import Data.Fin.Properties
open import Data.Nat.Base
open import Data.Product as Σ using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
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

module _ {P : Pred A p} {Q : Pred B q} {f : A → B} where

  map⁺ :  (∀ {x} → P x → Q (f x)) →
          ∀ {n xs} → All P {n = n} xs → All Q (VF.map f xs)
  map⁺ pq ps i = pq (ps i)

------------------------------------------------------------------------
-- replicate

module _ {P : Pred A p} {x : A} {n : ℕ} where

  replicate⁺ : P x → All P (replicate {n = n} x)
  replicate⁺ = const

------------------------------------------------------------------------
-- _⊛_

module _ {P : Pred A p} {Q : Pred B q} where

  ⊛⁺ : ∀ {n} {fs : Vector (A → B) n} {xs} →
       All (λ f → ∀ {x} → P x → Q (f x)) fs → All P xs → All Q (fs ⊛ xs)
  ⊛⁺ pqs ps i = (pqs i) (ps i)

------------------------------------------------------------------------
-- zipWith

module _ {P : Pred A p} {Q : Pred B q} {R : Pred C r} where

  zipWith⁺ : ∀ {f} → (∀ {x y} → P x → Q y → R (f x y)) → ∀ {n xs ys} →
             All P xs → All Q ys → All R (zipWith f {n = n} xs ys)
  zipWith⁺ pqr ps qs i = pqr (ps i) (qs i)

------------------------------------------------------------------------
-- zip

module _ {P : Pred A p} {Q : Pred B q} {n} {xs : Vector A n} {ys} where

  zip⁺ : All P xs → All Q ys → All (P ⟨×⟩ Q) (zip xs ys)
  zip⁺ ps qs i = ps i , qs i

  zip⁻ : All (P ⟨×⟩ Q) (zip xs ys) → All P xs × All Q ys
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

module _ (P : Pred A p) {m n : ℕ} {xs : Vector A m} {ys : Vector A n} where

  ++⁺ : All P xs → All P ys → All P (xs ++ ys)
  ++⁺ pxs pys i with splitAt m i
  ... | inj₁ i′ = pxs i′
  ... | inj₂ j′ = pys j′

module _ (P : Pred A p) {m n : ℕ} (xs : Vector A m) {ys : Vector A n} where

  ++⁻ˡ : All P (xs ++ ys) → All P xs
  ++⁻ˡ ps i with ps (inject+ n i)
  ... | p rewrite splitAt-inject+ m n i = p

  ++⁻ʳ : All P (xs ++ ys) → All P ys
  ++⁻ʳ ps i with ps (raise m i)
  ... | p rewrite splitAt-raise m n i = p

  ++⁻ : All P (xs ++ ys) → All P xs × All P ys
  ++⁻ ps = ++⁻ˡ ps , ++⁻ʳ ps
