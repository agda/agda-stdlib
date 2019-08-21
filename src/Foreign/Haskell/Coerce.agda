------------------------------------------------------------------------
-- The Agda standard library
--
-- Zero-cost coercion to cross the FFI boundary
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Foreign.Haskell.Coerce where

------------------------------------------------------------------------
-- Motivation

-- Problem: No COMPILE directives for common inductive types

-- In order to guarantee that the vast majority of the libary is
-- considered safe by Agda, we had to remove the COMPILE pragmas
-- associated to common inductive types.
-- These directives cannot possibly be checked by the compiler and
-- the user could define unsound mappings (e.g. swapping Bool's
-- true and false).

-- Solution: Essentially identical definitions + zero-cost coercions

-- To solve this problem, we have introduced a number of essentially
-- identical definitions in the Foreign.Haskell.* modules. However
-- converting back and forth between the FFI-friendly type and its
-- safe counterpart would take linear time.
-- This module defines zero cost coercions between these types.

------------------------------------------------------------------------
-- Definition

open import Level using (Level; _⊔_)
open import Agda.Builtin.Nat
open import Agda.Builtin.Int

import Data.Maybe.Base as STD
import Data.Product    as STD

import Foreign.Haskell.Maybe as FFI
import Foreign.Haskell.Pair  as FFI

private
  variable
    a b c d e f : Level
    A : Set a
    B : Set b
    C : Set c
    D : Set d

-- We postulate a type `Coercible`. A value of `Coercible A B` is a
-- proof that ̀A` and `B` have the same underlying representation.

postulate Coercible : (A : Set a) (B : Set b) → Set (a ⊔ b)

{-# FOREIGN GHC type AgdaCoerce l1 l2 a b = () #-}
{-# COMPILE GHC Coercible = type AgdaCoerce #-}

-- Once we get our hands on a proof that `Coercible A B` we know that
-- it is safe to an `A` to a `B`. This is done by using `unsafeCoerce`.

postulate coerce : {{Coercible A B}} → A → B

{-# FOREIGN GHC import Unsafe.Coerce #-}
{-# COMPILE GHC coerce = \ _ _ _ _ _ -> unsafeCoerce #-}

------------------------------------------------------------------------
-- Variants

Coercible₁ : ∀ a c → (T : Set a → Set b) (U : Set c → Set d) → Set _
Coercible₁ _ _ T U = ∀ {A B} → {{Coercible A B}} → Coercible (T A) (U B)

Coercible₂ : ∀ a b d e → (T : Set a → Set b → Set c) (U : Set d → Set e → Set f) → Set _
Coercible₂ _ _ _ _ T U = ∀ {A B} → {{Coercible A B}} → Coercible₁ _ _ (T A) (U B)

------------------------------------------------------------------------
-- Instances

-- Nat

-- Our first example of such a case reveals one of Agda's secrets:
-- natural numbers are represented by (arbitrary precision) integers
-- at runtime! Note that we may only coerce in one direction: integers
-- may actually be negative.

instance
  postulate
    nat-toInt : Coercible Nat Int

-- Maybe

instance
  postulate
    maybe-toFFI   : Coercible₁ a b STD.Maybe FFI.Maybe
    maybe-fromFFI : Coercible₁ a b FFI.Maybe STD.Maybe

-- Product

instance
  postulate
    pair-toFFI   : Coercible₂ a b c d STD._×_ FFI.Pair
    pair-fromFFI : Coercible₂ a b c d FFI.Pair STD._×_

-- Function

-- Functions are contravariant in their domain.

instance
  postulate
    coerce-fun : {{Coercible A B}} → Coercible₁ c d (λ C → B → C) (λ D → A → D)

-- Reflexivity

instance
  postulate
    coerce-refl : Coercible A A
