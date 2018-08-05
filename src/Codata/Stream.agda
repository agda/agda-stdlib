------------------------------------------------------------------------
-- The Agda standard library
--
-- The Stream type and some operations
------------------------------------------------------------------------

module Codata.Stream where

open import Size
open import Codata.Thunk

open import Data.Nat.Base
open import Data.Vec using (Vec ; [] ; _∷_)
open import Data.Product as P hiding (map)

------------------------------------------------------------------------
-- Definition

data Stream {ℓ} (A : Set ℓ) (i : Size) : Set ℓ where
  _∷_ : A → Thunk (Stream A) i → Stream A i

module _ {ℓ} {A : Set ℓ} where

 repeat : ∀ {i} → A → Stream A i
 repeat a = a ∷ λ where .force → repeat a

 head : ∀ {i} → Stream A i → A
 head (x ∷ xs) = x

 tail : Stream A ∞ → Stream A ∞
 tail (x ∷ xs) = xs .force

 lookup : ℕ → Stream A ∞ → A
 lookup zero    xs = head xs
 lookup (suc k) xs = lookup k (tail xs)

 take : (n : ℕ) → Stream A ∞ → Vec A n
 take zero    xs = []
 take (suc n) xs = head xs ∷ take n (tail xs)

module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} where

 map : ∀ {i} → (A → B) → Stream A i → Stream B i
 map f (x ∷ xs) = f x ∷ λ where .force → map f (xs .force)

 ap : ∀ {i} → Stream (A → B) i → Stream A i → Stream B i
 ap (f ∷ fs) (x ∷ xs) = f x ∷ λ where .force → ap (fs .force) (xs .force)

 unfold : ∀ {i} → (A → A × B) → A → Stream B i
 unfold next seed =
   let (seed′ , b) = next seed in
   b ∷ λ where .force → unfold next seed′

 scanl : ∀ {i} → (B → A → B) → B → Stream A i → Stream B i
 scanl c n (x ∷ xs) = n ∷ λ where .force → scanl c (c n x) (xs .force)

module _ {ℓ ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} where

 zipWith : ∀ {i} → (A → B → C) → Stream A i → Stream B i → Stream C i
 zipWith f (a ∷ as) (b ∷ bs) = f a b ∷ λ where .force → zipWith f (as .force) (bs .force)

module _ {ℓ} {A : Set ℓ} where

 iterate : ∀ {i} → (A → A) → A → Stream A i
 iterate f a = a ∷ λ where .force → map f (iterate f a)



------------------------------------------------------------------------
-- Legacy

open import Coinduction
import Codata.Musical.Stream as M

fromMusical : ∀ {a} {A : Set a} → M.Stream A → ∀ {i} → Stream A i
fromMusical (x M.∷ xs) = x ∷ λ where .force → fromMusical (♭ xs)
