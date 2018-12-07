module Data.Nat.Instance where

open import Data.Nat
open import Relation.Binary
open import Level hiding (zero ; suc)

data _≤ᵢ_ : Rel ℕ 0ℓ where
  instance
    z≤n : ∀ {n}                   → zero  ≤ᵢ n
    s≤s : ∀ {m n} {{m≤n : m ≤ᵢ n}} → suc m ≤ᵢ suc n


≤ᵢ-to-≤ : ∀{a b} → {{rl : a ≤ᵢ b}} → a ≤ b 
≤ᵢ-to-≤ {{z≤n}} = z≤n
≤ᵢ-to-≤ {{s≤s}} = s≤s ≤ᵢ-to-≤

≤-to-≤ᵢ : ∀{a b} → a ≤ b → a ≤ᵢ b
≤-to-≤ᵢ z≤n = z≤n
≤-to-≤ᵢ (s≤s x) = s≤s {{≤-to-≤ᵢ x}}


