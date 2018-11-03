------------------------------------------------------------------------
-- The Agda standard library
--
-- The Stream type and some operations
------------------------------------------------------------------------

module Codata.Stream where

open import Size
open import Codata.Thunk as Thunk using (Thunk; force)

open import Data.Nat.Base
open import Data.List.Base using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Vec using (Vec; []; _∷_)
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

 infixr 5 _++_ _⁺++_
 _++_ : ∀ {i} → List A → Stream A i → Stream A i
 []       ++ ys = ys
 (x ∷ xs) ++ ys = x ∷ λ where .force → xs ++ ys

 _⁺++_ : ∀ {i} → List⁺ A → Thunk (Stream A) i → Stream A i
 (x ∷ xs) ⁺++ ys = x ∷ λ where .force → xs ++ ys .force

 cycle : ∀ {i} → List⁺ A → Stream A i
 cycle xs = xs ⁺++ λ where .force → cycle xs

 concat : ∀ {i} → Stream (List⁺ A) i → Stream A i
 concat (xs ∷ xss) = xs ⁺++ λ where .force → concat (xss .force)

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

open import Codata.Musical.Notation using (♭; ♯_)
import Codata.Musical.Stream as M

module _ {a} {A : Set a} where

  fromMusical : ∀ {i} → M.Stream A → Stream A i
  fromMusical (x M.∷ xs) = x ∷ λ where .force → fromMusical (♭ xs)

  toMusical : Stream A ∞ → M.Stream A
  toMusical (x ∷ xs) = x M.∷ ♯ toMusical (xs .force)
