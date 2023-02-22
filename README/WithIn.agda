------------------------------------------------------------------------
-- The Agda standard library
--
-- Explaining how to use the `with ... in ...` idiom.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module README.WithIn where

open import Data.Nat.Base
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Using `with ... in ...`

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

-- This is where we can use `with ... in ...`. By using `with f x in eq`, we get
-- *both* a `y` which is the result of `f x` *and* a proof `eq` that `f x ≡ y`.
-- Splitting on the result of `m + n`, we get two cases:

-- 1. `m ≡ 0 × n ≡ 0` under the assumption that `m + n ≡ zero`
-- 2. `m + n ≡ suc p` under the assumption that `m + n ≡ suc p`

-- The first one can be discharged using lemmas from Data.Nat.Properties and
-- the second one is trivial.

plus-eq-with-in : ∀ m n → Plus-eq m n (m + n)
plus-eq-with-in m n with m + n in eq
... | zero  = m+n≡0⇒m≡0 m eq , m+n≡0⇒n≡0 m eq
... | suc p = eq

-- NB. What has been lost? the new syntax binds `eq` once and for all,
-- whereas the old `with ... inspect` syntax allowed pattern-matching on
-- *different names* for the equation in each possible branch after a `with`.

------------------------------------------------------------------------
-- Understanding the implementation of `with ... in ...`

-- What happens if we try to avoid use of the ̀with ... in ...` syntax?
-- The fact is: we don't have to if we write our own auxiliary lemma:

plus-eq-aux : ∀ m n → Plus-eq m n (m + n)
plus-eq-aux m n = aux m n (m + n) refl where

  aux : ∀ m n p → m + n ≡ p → Plus-eq m n p
  aux m n zero    m+n≡0   = m+n≡0⇒m≡0 m m+n≡0 , m+n≡0⇒n≡0 m m+n≡0
  aux m n (suc p) m+n≡1+p = m+n≡1+p

-- NB. Here we can choose alternative names in each branch of `aux`
-- for the proof of the auxiliary hypothesis `m + n ≡ p`

-- We could likewise emulate the general behaviour of `with ... in ...`
-- using an auxiliary function as follows, using the `with p ← ...` syntax
-- to bind the subexpression `m + n` to (pattern) variable `p`:

plus-eq-with-in-aux : ∀ m n → Plus-eq m n (m + n)
plus-eq-with-in-aux m n with p ← m + n in eq = aux m n p eq where

  aux : ∀ m n p → m + n ≡ p → Plus-eq m n p
  aux m n zero    m+n≡0   = m+n≡0⇒m≡0 m m+n≡0 , m+n≡0⇒n≡0 m m+n≡0
  aux m n (suc p) m+n≡1+p = m+n≡1+p

-- That is, more or less, what the Agda-generated definition corresponding to
-- `plus-eq-with-in` would look like.
