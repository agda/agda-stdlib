------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties related to All
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Vec.Functional.Relation.Unary.All.Properties where

open import Data.Nat.Base using (ℕ)
open import Data.Fin.Base using (zero; suc; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt-↑ˡ; splitAt-↑ʳ)
open import Data.Product.Base as Σ using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Vec.Functional as VF hiding (map)
open import Data.Vec.Functional.Relation.Unary.All
open import Function.Base using (const; _∘_)
open import Level using (Level)
open import Relation.Unary using (Pred; _⟨×⟩_)

private
  variable
    a p ℓ : Level
    A B C : Set a
    P Q R : Pred A p
    m n : ℕ
    x y : A
    xs ys : Vector A n

------------------------------------------------------------------------
-- map

map⁺ :  ∀ {f : A → B} → (∀ {x} → P x → Q (f x)) →
        All P xs → All Q (VF.map f xs)
map⁺ pq ps i = pq (ps i)

------------------------------------------------------------------------
-- replicate

replicate⁺ : P x → All P (replicate n x)
replicate⁺ = const

------------------------------------------------------------------------
-- _⊛_

⊛⁺ : ∀ {fs : Vector (A → B) n} →
     All (λ f → ∀ {x} → P x → Q (f x)) fs →
     All P xs → All Q (fs ⊛ xs)
⊛⁺ pqs ps i = (pqs i) (ps i)

------------------------------------------------------------------------
-- zipWith

zipWith⁺ : ∀ {f} → (∀ {x y} → P x → Q y → R (f x y)) →
           All P xs → All Q ys → All R (zipWith f xs ys)
zipWith⁺ pqr ps qs i = pqr (ps i) (qs i)

------------------------------------------------------------------------
-- zip

zip⁺ : All P xs → All Q ys → All (P ⟨×⟩ Q) (zip xs ys)
zip⁺ ps qs i = ps i , qs i

zip⁻ : All (P ⟨×⟩ Q) (zip xs ys) → All P xs × All Q ys
zip⁻ pqs = proj₁ ∘ pqs , proj₂ ∘ pqs

------------------------------------------------------------------------
-- head

head⁺ : ∀ (P : Pred A p) → All P xs → P (head xs)
head⁺ P ps = ps zero

------------------------------------------------------------------------
-- tail

tail⁺ : ∀ (P : Pred A p) → All P xs → All P (tail xs)
tail⁺ P xs = xs ∘ suc

------------------------------------------------------------------------
-- ++

module _ (P : Pred A p) {xs : Vector A m} {ys : Vector A n} where

  ++⁺ : All P xs → All P ys → All P (xs ++ ys)
  ++⁺ pxs pys i with splitAt m i
  ... | inj₁ i′ = pxs i′
  ... | inj₂ j′ = pys j′

module _ (P : Pred A p) (xs : Vector A m) {ys : Vector A n} where

  ++⁻ˡ : All P (xs ++ ys) → All P xs
  ++⁻ˡ ps i with ps (i ↑ˡ n)
  ... | p rewrite splitAt-↑ˡ m i n = p

  ++⁻ʳ : All P (xs ++ ys) → All P ys
  ++⁻ʳ ps i with ps (m ↑ʳ i)
  ... | p rewrite splitAt-↑ʳ m n i = p

  ++⁻ : All P (xs ++ ys) → All P xs × All P ys
  ++⁻ ps = ++⁻ˡ ps , ++⁻ʳ ps
