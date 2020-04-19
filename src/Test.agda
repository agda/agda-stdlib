
module Test where

open import Data.Unit using (tt)
open import Data.Nat
open import Data.Bool
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

NonZero₁ : ℕ → Set
NonZero₁ n = T (0 <ᵇ n) --True (0 <ᵇ n)

_/₁_ : ∀ (m n : ℕ) → {{.(NonZero₁ n)}} → ℕ
m /₁ suc n = n

test : ∀ m n → m /₁ (suc n) ≡ n
test = {!NonZero₁ 1!}
