------------------------------------------------------------------------
-- The Agda standard library
--
-- Examples showing how the generic n-ary operations the stdlib provides
-- can be used
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.N-ary where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Fin using (#_)
open import Data.Product
open import Data.Product.N-ary.Heterogeneous
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Cong

_ : ∀ m n p q → suc (m + (p * n) + (q ^ (m + n)))
              ≡ (m + 0) + (n * p) + (q ^ m * q ^ n) + 1
_ = λ m n p q → begin
    suc (m + (p * n) + (q ^ (m + n))) ≡⟨ +-comm 1 _ ⟩
    m + (p * n) + (q ^ (m + n)) + 1   ≡⟨ congₙ 3 (λ m n p → m + n + p + 1)
                                                 (+-comm 0 m)
                                                 (*-comm p n)
                                                 (^-distribˡ-+-* q m n)
                                       ⟩
    m + 0 + n * p + (q ^ m) * (q ^ n) + 1 ∎ where open ≡-Reasoning

-- Partial application of the functional argument is fine: the number of arguments
-- `congₙ` is going to take is determined by its first argument (a natural number)
-- and not by the type of the function it works on.

_ : ∀ m → (m +_) ≡ ((m + 0) +_)
_ = λ m → congₙ 1 _+_ (+-comm 0 m)

-- We don't have to work on the function's first argument either: we can just as
-- easily use `congₙ` to act on the second one by `flip`ping it.

_ : ∀ m → (_+ m) ≡ (_+ (m + 0))
_ = λ m → congₙ 1 (flip _+_) (+-comm 0 m)

-----------------------------------------------------------------------
-- Subst

open import Agda.Builtin.Nat using (mod-helper)

-- Because we know from the definition `mod-helper` that this equation holds:
-- mod-helper k m (suc n) (suc j) = mod-helper (suc k) m n j
-- we should be able to prove the slightly modified statement by transforming
-- all the `x + 1` into `suc x`. We can do so using `substₙ`.

_ : ∀ k m n j → mod-helper k m (n + 1) (j + 1) ≡ mod-helper (k + 1) m n j
_ = λ k m n j →
    let P sk sn sj = mod-helper k m sn sj ≡ mod-helper sk m n j
    in substₙ 3 P (+-comm 1 k) (+-comm 1 n) (+-comm 1 j) refl

-----------------------------------------------------------------------
-- (Un)curry

module _ {a b c d e} {A : Set a} {B : Set b} {C : Set c} {D : Set d} {E : Set e} where

  example₁ : (A × (B × C) × D → E) → A → B × C → D → E
  example₁ = curryₙ 3

  example₂ : (A → B → C → D → E) → A → B → (C × D) → E
  example₂ = curryₙ 3 ∘′ uncurryₙ 4

-----------------------------------------------------------------------
-- Projections

  proj₃ : (A × B × C × D × E) → C
  proj₃ = projₙ 5 (# 2)

  proj₃' : (A × B × C × D × E) → C × D × E
  proj₃' = projₙ 3 (# 2)

  insert₃ : C → (A × B × D × E) → (A × B × C × D × E)
  insert₃ = insertₙ 4 (# 2)

  insert-last : C → (A × B × D × E) → (A × B × D × E × C)
  insert-last = insertₙ 4 (# 4)

  remove₃ :  (A × B × C × D × E) → (A × B × D × E)
  remove₃ = removeₙ 5 (# 2)
