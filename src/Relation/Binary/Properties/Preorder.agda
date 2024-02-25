------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties satisfied by preorders
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Preorder; Setoid)
open import Relation.Binary.Structures using (IsPreorder)

module Relation.Binary.Properties.Preorder
  {p₁ p₂ p₃} (P : Preorder p₁ p₂ p₃) where

open import Function.Base using (flip)
open import Data.Product.Base as Product using (_×_; _,_; swap)
import Relation.Binary.Construct.Flip.EqAndOrd as EqAndOrd

open Preorder P


------------------------------------------------------------------------
-- The converse relation is also a preorder.

converse-isPreorder : IsPreorder _≈_ _≳_
converse-isPreorder = EqAndOrd.isPreorder isPreorder

converse-preorder : Preorder p₁ p₂ p₃
converse-preorder = EqAndOrd.preorder P

------------------------------------------------------------------------
-- For every preorder there is an induced equivalence

InducedEquivalence : Setoid _ _
InducedEquivalence = record
  { _≈_           = λ x y → x ≲ y × x ≳ y
  ; isEquivalence = record
    { refl  = (refl , refl)
    ; sym   = swap
    ; trans = Product.zip trans (flip trans)
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
