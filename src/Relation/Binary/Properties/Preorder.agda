------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by preorders
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Properties.Preorder
  {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open import Function.Base
open import Data.Product as Prod
import Relation.Binary.Construct.Converse as Converse

open Preorder P

------------------------------------------------------------------------
-- The inverse relation is also a preorder.

converse-isPreorder : IsPreorder _≈_ (flip _∼_)
converse-isPreorder = Converse.isPreorder isPreorder

converse-preorder : Preorder p₁ p₂ p₃
converse-preorder = Converse.preorder P

------------------------------------------------------------------------
-- For every preorder there is an induced equivalence

InducedEquivalence : Setoid _ _
InducedEquivalence = record
  { _≈_           = λ x y → x ∼ y × y ∼ x
  ; isEquivalence = record
    { refl  = (refl , refl)
    ; sym   = swap
    ; trans = Prod.zip trans (flip trans)
    }
  }



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 2.0

invIsPreorder = converse-isPreorder
{-# WARNING_ON_USAGE invIsPreorder
"Warning: invIsPreorder was deprecated in v2.0.
Please use converse-isPreorder instead."
#-}
invPreorder = converse-preorder
{-# WARNING_ON_USAGE invPreorder
"Warning: invPreorder was deprecated in v2.0.
Please use converse-preorder instead."
#-}
