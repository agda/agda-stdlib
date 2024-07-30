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
-- Expressions and Normal forms

open module N = Normal M public
-- for deprecation below
  renaming (∙-homo to homomorphic; correct to normalise-correct)
  hiding (module Expr)

open N.Expr public
-- for backwards compatibility
  renaming (‵var to var; ‵ε to id; _‵∙_ to _⊕_)

------------------------------------------------------------------------
-- Tactic

open module T = Tactic M normal public
  hiding (prove)

prove : ∀ n (es : Expr n × Expr n) → From-just (uncurry prove′ es)
prove _ = from-just ∘ uncurry prove′


------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.2

{-# WARNING_ON_USAGE homomorphic
"Warning: homomorphic was deprecated in v2.2.
Please use (relevant field `homo` of) Algebra.Solver.Monoid.Normal.⟦⟧⇓-homo instead."
#-}

{-# WARNING_ON_USAGE normalise-correct
"Warning: normalise-correct was deprecated in v2.2.
Please use Algebra.Solver.Monoid.Normal.correct instead."
#-}

{-# WARNING_ON_USAGE var
"Warning: var was deprecated in v2.2.
Please use Algebra.Solver.Monoid.Expression.‵var instead."
#-}

{-# WARNING_ON_USAGE id
"Warning: id was deprecated in v2.2.
Please use Algebra.Solver.Monoid.Expression.‵ε instead."
#-}

{-# WARNING_ON_USAGE _⊕_
"Warning: _⊕_ was deprecated in v2.2.
Please use Algebra.Solver.Monoid.Expression._‵∙_ instead."
#-}

