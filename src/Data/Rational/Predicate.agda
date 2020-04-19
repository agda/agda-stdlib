------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple predicates over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Rational.Predicate where

open import Data.Rational.Base
open import Data.Integer as ℤ using (+0; -[1+_]; +[1+_]; _◃_; ∣_∣)
import Data.Integer.Predicate as ℤ
import Data.Integer.Properties as ℤ
open import Data.Nat using (zero; suc)
open import Data.Integer.Properties
open import Level using (0ℓ)
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≢_; refl; sym)
open import Relation.Unary using (Pred)

open ≤-Reasoning
