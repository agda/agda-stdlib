------------------------------------------------------------------------
-- The Agda standard library
--
-- Explaining how to use the inspect idiom and elaborating on the way
-- it is implemented in the standard library.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.Inspect where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Using inspect

-- We start with the definition of a (silly) predicate: `Plus m n p` states
-- that `m + n` is equal to `p` in a rather convoluted way. Crucially, it
-- distinguishes two cases: whether `p` is 0 or not.

Plus-eq : (m n p : ℕ) → Set
Plus-eq m n zero      = m ≡ 0 × n ≡ 0
Plus-eq m n p@(suc _) = m + n ≡ p

-- A sensible lemma to prove of this predicate is that whenever `p` is literally
-- `m + n` then `Plus m n p` holds. That is to say `∀ m n → Plus m n (m + n)`.
-- To be able to prove `Plus-eq m n (m + n)`, we need `m + n` to have either
-- the shape `zero` or `suc _` so that `Plus-eq` may reduce.

-- We could follow the way `_+_` computes by mimicking the same splitting
-- strategy, thus forcing `m + n` to reduce:

plus-eq-+ : ∀ m n → Plus-eq m n (m + n)
plus-eq-+ zero   zero    = refl , refl
plus-eq-+ zero   (suc n) = refl
plus-eq-+ (suc m) n      = refl

-- Or we could attempt to compute `m + n` first and check whether the result
-- is `zero` or `suc p`. By using `with m + n` and naming the result `p`,
-- the goal will become `Plus-eq m n p`. We can further refine this definition
-- by distinguishing two cases like so:

-- plus-eq-with : ∀ m n → Plus-eq m n (m + n)
-- plus-eq-with m n with m + n
-- ... | zero  = {!!}
-- ... | suc p = {!!}

-- The problem however is that we have abolutely lost the connection between the
-- computation `m + n` and its result `p`. Which makes the two goals unprovable:

-- 1. `m ≡ 0 × n ≡ 0`, with no assumption whatsoever
-- 2. `m + n ≡ suc p`, with no assumption either

-- By using the `with` construct, we have generated an auxiliary function that
-- looks like this:
-- `plus-eq-with-aux : ∀ m n p → Plus-eq m n p`
-- when we would have wanted a more precise type of the form:
-- `plus-eq-aux : ∀ m n p → m + n ≡ p → Plus-eq m n p`.

-- This is where we can use `inspect`. By using `with f x | inspect f x`,
-- we get both a `y` which is the result of `f x` and a proof that `f x ≡ y`.
-- Splitting on the result of `m + n`, we get two cases:

-- 1. `m ≡ 0 × n ≡ 0` under the assumption that `m + n ≡ zero`
-- 2. `m + n ≡ suc p` under the assumption that `m + n ≡ suc p`

-- The first one can be discharged using lemmas from Data.Nat.Properties and
-- the second one is trivial.

plus-eq-with : ∀ m n → Plus-eq m n (m + n)
plus-eq-with m n with m + n | inspect (m +_) n
... | zero  | [ m+n≡0   ] = i+j≡0⇒i≡0 m m+n≡0 , i+j≡0⇒j≡0 m m+n≡0
... | suc p | [ m+n≡1+p ] = m+n≡1+p


------------------------------------------------------------------------
-- Understanding the implementation of inspect

-- So why is it that we have to go through the record type `Reveal_·_is_`
-- and the ̀inspect` function? The fact is: we don't have to if we write
-- our own auxiliary lemma:

plus-eq-aux : ∀ m n → Plus-eq m n (m + n)
plus-eq-aux m n = aux m n (m + n) refl where

  aux : ∀ m n p → m + n ≡ p → Plus-eq m n p
  aux m n zero    m+n≡0   = i+j≡0⇒i≡0 m m+n≡0 , i+j≡0⇒j≡0 m m+n≡0
  aux m n (suc p) m+n≡1+p = m+n≡1+p

-- The problem is that when we write ̀with f x | pr`, `with` decides to call `y`
-- the result `f x` and to replace *all* of the occurences of `f x` in the type
-- of `pr` with `y`. That is to say that if we were to write:

-- plus-eq-naïve : ∀ m n → Plus-eq m n (m + n)
-- plus-eq-naïve m n with m + n | refl {x = m + n}
-- ... | p | eq = {!!}

-- then `with` would abstract `m + n` as `p` on *both* sides of the equality
-- proven by `refl` thus giving us the following goal with an extra, useless,
-- assumption:

-- 1. `Plus-eq m n p` under the assumption that `p ≡ p`

-- So how does `inspect` work? The standard library uses a more general version
-- of the following type and function:

record MyReveal_·_is_ (f : ℕ → ℕ) (x y : ℕ) : Set where
  constructor [_]
  field eq : f x ≡ y

my-inspect : ∀ f n → MyReveal f · n is (f n)
my-inspect f n = [ refl ]

-- Given that `inspect` has the type `∀ f n → Reveal f · n is (f n)`, when we
-- write `with f n | inspect f n`, the only `f n` that can be abstracted in the
-- type of `inspect f n` is the third argument to `Reveal_·_is_`.

-- That is to say that the auxiliary definition generated looks like this:

plus-eq-reveal : ∀ m n → Plus-eq m n (m + n)
plus-eq-reveal m n = aux m n (m + n) (my-inspect (m +_) n) where

  aux : ∀ m n p → MyReveal (m +_) · n is p → Plus-eq m n p
  aux m n zero    [ m+n≡0   ] = i+j≡0⇒i≡0 m m+n≡0 , i+j≡0⇒j≡0 m m+n≡0
  aux m n (suc p) [ m+n≡1+p ] = m+n≡1+p

-- At the cost of having to unwrap the constructor `[_]` around the equality
-- we care about, we can keep relying on `with` and avoid having to roll out
-- handwritten auxiliary definitions.
