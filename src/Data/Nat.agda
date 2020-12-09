------------------------------------------------------------------------
-- The Agda standard library
--
-- Natural numbers
------------------------------------------------------------------------

-- See README.Data.Nat for examples of how to use and reason about
-- naturals.

{-# OPTIONS --without-K --safe #-}

module Data.Nat where

open import Data.Bool.Base using (Bool; _∧_)
open import Data.Char.Base as Char using (Char)
open import Data.List.Base as List using (List)
open import Data.List.Categorical using (module TraversableA)
open import Data.Maybe.Base as Maybe using (Maybe; nothing; _<∣>_; when)
import Data.Maybe.Categorical as Maybe
open import Data.String.Base as String using (String)
open import Function.Base
open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- Publicly re-export the contents of the base module

open import Data.Nat.Base public

------------------------------------------------------------------------
-- Publicly re-export queries

open import Data.Nat.Properties public
  using
  ( _≟_
  ; _≤?_ ; _≥?_ ; _<?_ ; _>?_
  ; _≤′?_; _≥′?_; _<′?_; _>′?_
  ; _≤″?_; _<″?_; _≥″?_; _>″?_
  ; _<‴?_; _≤‴?_; _≥‴?_; _>‴?_
  )

------------------------------------------------------------------------
-- Reading a number

readMaybe : ∀ base {base≤16 : True (base ≤? 16)} → String → Maybe ℕ
readMaybe _ "" = nothing
readMaybe base = Maybe.map convert
              ∘′ TraversableA.mapA Maybe.applicative readDigit
              ∘′ String.toList

  where

    convert : List ℕ → ℕ
    convert = List.foldl (λ acc d → base * acc + d) 0

    char0 = Char.toℕ '0'
    char9 = Char.toℕ '9'
    chara = Char.toℕ 'a'
    charf = Char.toℕ 'f'

    readDigit : Char → Maybe ℕ
    readDigit c = digit Maybe.>>= λ n → when (n <ᵇ base) n where

      charc = Char.toℕ c

      dec = when ((char0 ≤ᵇ charc) ∧ (charc ≤ᵇ char9)) (charc ∸ char0)
      hex = when ((chara ≤ᵇ charc) ∧ (charc ≤ᵇ charf)) (charc ∸ chara)
      digit = dec <∣> hex


------------------------------------------------------------------------
-- Deprecated

-- Version 0.17

open import Data.Nat.Properties public
  using (≤-pred)
