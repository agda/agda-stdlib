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

import Data.List.Base  as STD
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

-- We define a simple indexed datatype `Coercible`. A value of `Coercible A B`
-- is a proof that ̀A` and `B` have the same underlying runtime representation.
-- The only possible proof is an incantation from the implementer begging to
-- be trusted.

-- We need this type to be concrete so that overlapping instances can be checked
-- for equality: we do not care what proof we get as long as we get one.

-- We need for it to be a data type rather than a record type so that Agda does
-- not mistakenly build arbitrary instances by η-expansion.

data Coercible (A : Set a) (B : Set b) : Set where
  TrustMe : Coercible A B

{-# FOREIGN GHC data AgdaCoercible l1 l2 a b = TrustMe #-}
{-# COMPILE GHC Coercible = data AgdaCoercible (TrustMe) #-}

-- Once we get our hands on a proof that `Coercible A B` we postulate that it
-- is safe to convert an `A` into a `B`. This is done under the hood by using
-- `unsafeCoerce`.

postulate coerce : {{_ : Coercible A B}} → A → B

{-# FOREIGN GHC import Unsafe.Coerce #-}
{-# COMPILE GHC coerce = \ _ _ _ _ _ -> unsafeCoerce #-}

------------------------------------------------------------------------
-- Unary and binary variants for covariant type constructors

Coercible₁ : ∀ a c → (T : Set a → Set b) (U : Set c → Set d) → Set _
Coercible₁ _ _ T U = ∀ {A B} → {{_ : Coercible A B}} → Coercible (T A) (U B)

Coercible₂ : ∀ a b d e → (T : Set a → Set b → Set c) (U : Set d → Set e → Set f) → Set _
Coercible₂ _ _ _ _ T U = ∀ {A B} → {{_ : Coercible A B}} → Coercible₁ _ _ (T A) (U B)

------------------------------------------------------------------------
-- Instances

-- Nat

-- Our first instance reveals one of Agda's secrets: natural numbers are
-- represented by (arbitrary precision) integers at runtime! Note that we
-- may only coerce in one direction: arbitrary integers may actually be
-- negative and will not do as mere natural numbers.

instance

  nat-toInt : Coercible Nat Int
  nat-toInt = TrustMe

-- We then proceed to state that data types from the standard library
-- can be converted to their FFI equivalents which are bound to actual
-- Haskell types.

-- Maybe

  maybe-toFFI : Coercible₁ a b STD.Maybe FFI.Maybe
  maybe-toFFI = TrustMe

  maybe-fromFFI : Coercible₁ a b FFI.Maybe STD.Maybe
  maybe-fromFFI = TrustMe

-- Product

  pair-toFFI : Coercible₂ a b c d STD._×_ FFI.Pair
  pair-toFFI = TrustMe

  pair-fromFFI : Coercible₂ a b c d FFI.Pair STD._×_
  pair-fromFFI = TrustMe

-- We follow up with purely structural rules for builtin data types which
-- already have known low-level representations.

-- List

  coerce-list : Coercible₁ a b STD.List STD.List
  coerce-list = TrustMe

-- Function
-- Note that functions are contravariant in their domain.

  coerce-fun : {{_ : Coercible A B}} → Coercible₁ c d (λ C → B → C) (λ D → A → D)
  coerce-fun = TrustMe

-- Finally we add a reflexivity proof to discharge all the dangling constraints
-- involving type variables and concrete builtin types such as `Bool`.

-- This rule overlaps with the purely structural ones: when attempting to prove
-- `Coercible (List A) (List A)`, should Agda use the proof obtained by `coerce-refl`
-- or the one obtained by `coerce-list coerce-refl`? Because we are using a
-- datatype with a single constructor these distinctions do not matter: both proofs
-- are definitionally equal.

  coerce-refl : Coercible A A
  coerce-refl = TrustMe
