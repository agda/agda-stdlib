------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers mod n, type and basic operations
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc; NonZero; NonTrivial; nonTrivial⇒nonZero; _<_; _∸_)

module Data.Integer.Modulo n .{{_ : NonTrivial n}} where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawNearSemiring; RawSemiring; RawRing)
open import Data.Integer.Base as ℤ using (ℤ; _◂_; signAbs)
open import Data.Nat.Bounded.Base as ℕ< hiding (fromℕ; _∼_; ≡-Mod)
import Data.Nat.Properties as ℕ
open import Data.Sign.Base as Sign using (Sign)
open import Data.Unit.Base using (⊤)
open import Function.Base using (id; _∘_; _$_; _on_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    m o : ℕ
    i j : ℕ< n

  instance
    _ = nonTrivial⇒nonZero n

  m∸n<m : ∀ m n → .{{NonZero m}} → .{{NonZero n}} → m ∸ n < m
  m∸n<m m@(suc _) n@(suc o) = ℕ.s≤s (ℕ.m∸n≤m _ o)

------------------------------------------------------------------------
-- Definition

-- Infixes
infix  8 -_
infixl 7 _*_
infixl 6 _+_

-- Type definition
ℤmod : Set
ℤmod = ℕ< n

-- Re-export
fromℕ : ℕ → ℤmod
fromℕ = ℕ<.fromℕ

-- Negation
-_ : ℤmod → ℤmod
- ⟦ m@zero ⟧< _    = ⟦0⟧<
- ⟦ m@(suc _) ⟧< _ = ⟦ n ∸ m ⟧< m∸n<m _ _

-- Addition
_+_ : ℤmod → ℤmod → ℤmod
i + j = fromℕ (⟦ i ⟧ ℕ.+ ⟦ j ⟧)

-- Multiplication
_*_ : ℤmod → ℤmod → ℤmod
i * j = fromℕ (⟦ i ⟧ ℕ.* ⟦ j ⟧)

------------------------------------------------------------------------
-- Quotient map from ℤ

_◃_ : Sign → ℤmod → ℤmod
Sign.+ ◃ j = j
Sign.- ◃ j = - j

fromℤ : ℤ → ℤmod
fromℤ i with s ◂ ∣i∣ ← signAbs i = s ◃ fromℕ ∣i∣

-- the _mod_ syntax

Mod : ℤ → ℤmod
Mod = fromℤ

syntax Mod {n = n} i = i mod n

-- Quotient equivalence relation on ℤ induced by `fromℤ`

_∼_ : Rel ℤ _
_∼_ = _≡_ on fromℤ

≡-Mod : Rel ℤ _
≡-Mod i j = i ∼ j

syntax ≡-Mod n i j = i ≡ j mod n

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
           --; rawNearSemiring to +-*-rawNearSemiring
           ; rawSemiring to +-*-rawSemiring
           )

------------------------------------------------------------------------
-- -- Postfix notation for when opening the module unparameterised

0ℤmod = ⟦0⟧<
1ℤmod = ⟦1⟧<

