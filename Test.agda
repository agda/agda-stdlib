

module Test where

open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Data.Nat.Base hiding (NonZero)
open import Data.Nat.DivMod using (_/_)

variable n : ℕ

isSuc : ℕ → Bool
isSuc (suc _) = true
isSuc _ = false

data ⊥ : Set where

isTrue : Bool → Set
isTrue true = ⊤
isTrue _    = ⊥

record NonZero (n : ℕ) : Set where
  field isNonZero : isTrue (isSuc n)

instance
  nonZero : NonZero (suc n)
  nonZero = record { isNonZero = tt }

test1 : {{NonZero n}} → ({{NonZero n}} → ℕ) → ℕ
test1 g = g

test2 : {{NonZero (3 + n)}} → ({{NonZero (3 + n)}} → ℕ) → ℕ
test2 g = g

test3 : ((n : ℕ) → {{NonZero n}} → ℕ) → ℕ
test3 g = g 2


fn : ℕ → ℕ → ℕ
fn zero zero   = zero
fn m@(suc _) n = m
fn _ n@(suc _) = n

instance
  fn-nonZeroˡ : ∀ {m n} {{_ : NonZero m}} → NonZero (fn m n)
  fn-nonZeroˡ {suc _} {_} = _

  fn-nonZeroʳ : ∀ {m n} {{_ : NonZero n}} → NonZero (fn m n)
  fn-nonZeroʳ {zero}  {suc _} = _
  fn-nonZeroʳ {suc _} {suc _} = _

fn2 : ℕ → ℕ → ℕ
fn2 zero      n = zero
fn2 m@(suc _) n = (m * n) / fn m n
