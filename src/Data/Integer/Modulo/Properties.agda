------------------------------------------------------------------------
-- The Agda standard library
--
-- Integers mod n, properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base as ℕ
  using (ℕ; zero; suc; NonZero; NonTrivial; _<_; _∸_)

module Data.Integer.Modulo.Properties (n : ℕ) .{{_ : NonTrivial n}} where

open import Algebra.Bundles.Raw
  using (RawMagma; RawMonoid; RawNearSemiring; RawSemiring; RawRing)
open import Algebra.Bundles
  using (Magma; Monoid; NearSemiring; Semiring; Ring)
import Algebra.Definitions as Definitions
import Algebra.Structures as Structures
open import Data.Integer.Base as ℤ using (ℤ; _◂_; signAbs)
--open import Data.Nat.Bounded as ℕ< hiding (π; module Literals)
import Data.Nat.DivMod as ℕ
import Data.Nat.Properties as ℕ
open import Data.Sign.Base as Sign using (Sign)
open import Data.Unit.Base using (⊤)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; cong₂)

open import Data.Integer.Modulo n as Modulo using (ℤmod_; +-*-rawRing)
open Definitions (_≡_ {A = ℤmod_})
open Structures (_≡_ {A = ℤmod_})
  using (IsMagma; IsMonoid; IsAbelianGroup; IsNearSemiring; IsSemiring; IsRing)

private
  variable
    m o : ℕ
    i j k : ℤmod_

  instance
    _ = ℕ.nonTrivial⇒nonZero n

open RawRing +-*-rawRing

+-0-isAbelianGroup : IsAbelianGroup _+_ 0# -_
+-0-isAbelianGroup = {!!}

*-cong₂ : Congruent₂ _*_
*-cong₂ = cong₂ _*_

*-assoc : Associative _*_
*-assoc x y z = {!!}

*-identity : Identity 1# _*_
*-identity = {!!}

*-distrib-+ : _*_ DistributesOver _+_
*-distrib-+ = {!!}

+-*-isRing : IsRing _+_ _*_ -_ 0# 1#
+-*-isRing = record
  { +-isAbelianGroup = +-0-isAbelianGroup
  ; *-cong           = *-cong₂
  ; *-assoc          = *-assoc
  ; *-identity       = *-identity
  ; distrib          = *-distrib-+
  }
