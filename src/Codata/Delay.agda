------------------------------------------------------------------------
-- The Agda standard library
--
-- The Delay type and some operations
------------------------------------------------------------------------

module Codata.Delay where

open import Size
open import Codata.Thunk
open import Codata.Conat
open import Data.Nat.Base
open import Data.Maybe.Base hiding (map)

data Delay {ℓ} (A : Set ℓ) (i : Size) : Set ℓ where
  now   : A → Delay A i
  later : Thunk (Delay A) i → Delay A i

module _ {ℓ} {A : Set ℓ} where

 length : ∀ {i} → Delay A i → Conat i
 length (now _)   = zero
 length (later d) = suc λ where .force → length (d .force)

 never : ∀ {i} → Delay A i
 never = later λ where .force → never

 runFor : ℕ → Delay A ∞ → Maybe A
 runFor zero    d         = nothing
 runFor (suc n) (now a)   = just a
 runFor (suc n) (later d) = runFor n (d .force)

module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} where

 map : (A → B) → ∀ {i} → Delay A i → Delay B i
 map f (now a)   = now (f a)
 map f (later d) = later λ where .force → map f (d .force)

 bind : ∀ {i} → Delay A i → (A → Delay B i) → Delay B i
 bind (now a)   f = f a
 bind (later d) f = later λ where .force → bind (d .force) f

module _ {ℓ ℓ₁ ℓ₂} {A : Set ℓ} {B : Set ℓ₁} {C : Set ℓ₂} where

 zipWith : (A → B → C) → ∀ {i} → Delay A i → Delay B i → Delay C i
 zipWith f (now a)   d         = map (f a) d
 zipWith f d         (now b)   = map (λ a → f a b) d
 zipWith f (later a) (later b) = later λ where .force → zipWith f (a .force) (b .force)
