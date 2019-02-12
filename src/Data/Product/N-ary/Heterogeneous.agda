------------------------------------------------------------------------
-- The Agda standard library
--
-- Heterogeneous N-ary Products
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Product.N-ary.Heterogeneous where

open import Level as L using (Level; _⊔_; Lift)
open import Agda.Builtin.Unit
open import Data.Product
open import Data.Nat.Base using (ℕ; zero; suc)
open import Function

------------------------------------------------------------------------
-- Type Definition

-- We want to define n-ary products and generic n-ary operations on them
-- such as currying and uncurrying. We want users to be able to use these
-- seamlessly whenever n is concrete. In other words, we want Agda to infer
-- the sets `A₁, ⋯, Aₙ` when we write `uncurryₙ n f` where `f` has type
-- `A₁ → ⋯ → Aₙ → B`. For this to happen, we need the structure in which
-- these Sets are stored to effectively η-expand to `A₁, ⋯, Aₙ` when the
-- parameter `n` is known.
-- Hence the following definitions:

-- First, a "vector" of `n` Levels (defined by induction on n so that it
-- may be built by η-expansion and unification). Each Level will be that
-- of one of the Sets we want to take the n-ary product of.

Levels : ℕ → Set
Levels zero    = ⊤
Levels (suc n) = Level × Levels n

-- The overall product's Level will be the least upper bound of all of the
-- Levels involved.

toLevel : ∀ n → Levels n → Level
toLevel zero    _        = L.zero
toLevel (suc n) (l , ls) = l ⊔ toLevel n ls

-- Second, a "vector" of `n` Sets whose respective Levels are determined
-- by the `Levels n` input.

Sets : ∀ n (ls : Levels n) → Set (L.suc (toLevel n ls))
Sets zero    _        = Lift _ ⊤
Sets (suc n) (l , ls) = Set l × Sets n ls

-- Third, the n-ary product itself: provided n Levels and a corresponding
-- "vector" of `n` Sets, we can build a big right-nested product type packing
-- a value for each one of these Sets.

Product : ∀ n {ls : Levels n} → Sets n ls → Set (toLevel n ls)
Product zero    _        = ⊤
Product (suc n) (a , as) = a × Product n as

------------------------------------------------------------------------
-- Generic Programs: (un)curry
-- see Relation.Binary.PropositionalEquality for other examples (congₙ, substₙ)

-- To be able to talk about (un)currying, we need to be able to form the
-- type `A₁ → ⋯ → Aₙ → B`. This is what `Arrows` does, by induction on `n`.

Arrows : ∀ n {r} {ls : Levels n} → Sets n ls → Set r → Set (toLevel n ls ⊔ r)
Arrows zero    _        b = b
Arrows (suc n) (a , as) b = a → Arrows n as b

-- Finally, we can define `curryₙ` and `uncurryₙ` converting back and forth
-- between `A₁ → ⋯ → Aₙ → B` and `(A₁ × ⋯ × Aₙ) → B` by induction on `n`.

curryₙ : ∀ n {ls : Levels n} {as : Sets n ls} {r} {b : Set r} →
         (Product n as → b) → Arrows n as b
curryₙ zero    f = f _
curryₙ (suc n) f = curryₙ n ∘′ curry f

uncurryₙ : ∀ n {ls : Levels n} {as : Sets n ls} {r} {b : Set r} →
           Arrows n as b → (Product n as → b)
uncurryₙ zero    f = const f
uncurryₙ (suc n) f = uncurry (uncurryₙ n ∘′ f)
