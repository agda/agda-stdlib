------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers mod n, type and basic operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc; NonZero; NonTrivial; _<_; _∸_)

module Data.Integer.Modulo (n : ℕ) .{{_ : NonTrivial n}} where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawNearSemiring; RawSemiring; RawRing)
open import Data.Integer.Base as ℤ using (ℤ; _◂_; signAbs)
open import Data.Nat.Bounded as ℕ< hiding (π; module Literals)
open import Data.Nat.DivMod as ℕ using (_%_)
open import Data.Nat.Properties as ℕ
import Data.Sign.Base as Sign
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    m o : ℕ
    i j : ℕ< n

  instance
    _ = ℕ.nonTrivial⇒nonZero n

  m∸n<m : ∀ m n → .{{NonZero m}} → .{{NonZero n}} → m ∸ n < m
  m∸n<m m@(suc _) n@(suc o) = ℕ.s≤s (m∸n≤m _ o)

------------------------------------------------------------------------
-- Definition

-- Infixes
infix  8 -_
infixl 7 _*_
infixl 6 _+_

-- Type definition
ℤmod : Set
ℤmod = ℕ< n

-- Negation
-_ : ℤmod → ℤmod
- ⟦ m@zero ⟧< _    = ⟦0⟧<
- ⟦ m@(suc _) ⟧< _ = ⟦ n ∸ m ⟧< m∸n<m _ _

-- Addition
_+_ : ℤmod → ℤmod → ℤmod
i + j = ℕ<.π (⟦ i ⟧ ℕ.+ ⟦ j ⟧)

-- Multiplication
_*_ : ℤmod → ℤmod → ℤmod
i * j = ℕ<.π (⟦ i ⟧ ℕ.* ⟦ j ⟧)

------------------------------------------------------------------------
-- Quotient map from ℤ

_◃_ : Sign → ℤmod → ℤmod
Sign.+ ◃ j = j
Sign.- ◃ j = - j

π : ℤ → ℤmod
π i with s ◂ ∣i∣ ← signAbs i = s ◃ ℕ<.π ∣i∣ 

-- the _mod_ syntax
Mod : ℤ → ℤmod
Mod = π

syntax Mod {n = n} i = i mod n

------------------------------------------------------------------------
-- Raw bundles

+-*-rawRing : RawRing _ _
+-*-rawRing = record
  { _≈_ = _≡_
  ; _+_ = _+_
  ; _*_ = _*_
  ; -_ = -_
  ; 0# = ⟦0⟧<
  ; 1# = ⟦1⟧<
  }

open RawRing +-*-rawRing public
  using (+-rawMagma; *-rawMagma)
  renaming ( +-rawMonoid to +-0-rawMonoid
           ; *-rawMonoid to *-1-rawMonoid
           ; rawNearSemiring to +-*-rawNearSemiring
           ; rawSemiring to +-*-rawSemiring
           )

------------------------------------------------------------------------
-- Literals

module Literals where

  Constraint : ℕ → Set
  Constraint _ = ⊤

  fromNat : ∀ m → {{Constraint m}} → ℤmod
  fromNat m = ℕ<.π m

