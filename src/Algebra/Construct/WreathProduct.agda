------------------------------------------------------------------------
-- The Agda standard library
--
-- The Wreath Product of a Monoid N with a Monoid Action of M on A
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (Monoid)
open import Algebra.Construct.MonoidAction using (RawLeftAction; LeftAction)
open import Relation.Binary.Bundles using (Setoid)

module Algebra.Construct.WreathProduct
  {b c ℓb ℓc a r} {M : Monoid b ℓb} {A : Setoid a r}
  {rawLeftAction : RawLeftAction (Monoid._≈_ M) (Setoid._≈_ A)}
  (M∙A : LeftAction M A rawLeftAction) (N : Monoid c ℓc)
  where

open import Algebra.Bundles.Raw using (RawMonoid)
open import Algebra.Structures using (IsMonoid)

open import Data.Product.Base using (_,_; _×_)

open import Function.Base using (flip)

open import Level using (Level; suc; _⊔_)

open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Binary.Definitions

open module M = Monoid M using () renaming (Carrier to M)
open module N = Monoid N using () renaming (Carrier to N)
open module A = Setoid A using (_≈_) renaming (Carrier to A)

private
  variable
    x y z : A.Carrier
    m m′ m″ : M.Carrier
    n n′ n″ : N.Carrier


------------------------------------------------------------------------
-- Infix notation for when opening the module unparameterised

infixl 4 _⋊_
_⋊_ = {!monoidᵂ!}
