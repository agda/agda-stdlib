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
  renaming (comp-correct to homomorphic; correct to normalise-correct)

------------------------------------------------------------------------
-- Tactic

open module T = Tactic M (record { N }) public
  hiding (prove)

prove : ∀ n (es : Expr n × Expr n) → From-just (uncurry prove′ es)
prove _ = from-just ∘ uncurry prove′


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.1

{-# WARNING_ON_USAGE homomorphic
"Warning: homomorphic was deprecated in v2.1.
Please use Algebra.Solver.Monoid.Normal.comp-correct instead."
#-}

{-# WARNING_ON_USAGE normalise-correct
"Warning: normalise-correct was deprecated in v2.1.
Please use Algebra.Solver.Monoid.Normal.correct instead."
#-}
