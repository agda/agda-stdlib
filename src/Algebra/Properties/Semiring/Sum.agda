------------------------------------------------------------------------
-- The Agda standard library
--
-- Finite summations over a semiring
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Bundles using (Semiring)

module Algebra.Properties.Semiring.Sum {c} {ℓ} (R : Semiring c ℓ) where

open import Data.Nat.Base using (zero; suc)
open import Data.Vec.Functional
open Semiring R

------------------------------------------------------------------------
-- Re-export summation over monoids

open import Algebra.Properties.CommutativeMonoid.Sum +-commutativeMonoid public

------------------------------------------------------------------------
-- Properties

*-distribˡ-sum : ∀ {n} x (ys : Vector Carrier n) → x * sum ys ≈ sum (map (x *_) ys)
*-distribˡ-sum {zero} x ys = zeroʳ x
*-distribˡ-sum {suc n} x ys = trans (distribˡ x (head ys) (sum (tail ys))) (+-congˡ (*-distribˡ-sum x (tail ys)))

*-distribʳ-sum : ∀ {n} x (ys : Vector Carrier n) → sum ys * x ≈ sum (map (_* x) ys)
*-distribʳ-sum {zero} x ys = zeroˡ x
*-distribʳ-sum {suc n} x ys = trans (distribʳ x (head ys) (sum (tail ys))) (+-congˡ (*-distribʳ-sum x (tail ys)))
