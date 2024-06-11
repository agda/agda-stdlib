------------------------------------------------------------------------
-- The Agda standard library
--
-- A solver for equations over monoids
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)

module Algebra.Solver.Monoid {c ℓ} (M : Monoid c ℓ) where

import Algebra.Solver.Monoid.Normal as Normal
import Algebra.Solver.Monoid.Tactic as Tactic
open import Data.Maybe.Base as Maybe
  using (From-just; from-just)
open import Data.Product.Base using (_×_; uncurry)
open import Function.Base using (_∘_)

------------------------------------------------------------------------
-- Normal forms

open module N = Normal M public

------------------------------------------------------------------------
-- Tactic

open module T = Tactic M (record { N }) public
  hiding (prove)

prove : ∀ n (es : Expr n × Expr n) → From-just (uncurry prove′ es)
prove _ = from-just ∘ uncurry prove′
