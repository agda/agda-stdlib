------------------------------------------------------------------------
-- The Agda standard library
--
-- Signs
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Sign.Base where

open import Algebra.Bundles.Raw using (RawMagma; RawMonoid; RawGroup)
open import Level using (0ℓ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

------------------------------------------------------------------------
-- Definition

data Sign : Set where
  - : Sign
  + : Sign

------------------------------------------------------------------------
-- Operations

-- The opposite sign.

opposite : Sign → Sign
opposite - = +
opposite + = -

-- "Multiplication".

infixl 7 _*_

_*_ : Sign → Sign → Sign
+ * s₂ = s₂
- * s₂ = opposite s₂

------------------------------------------------------------------------
-- Raw Bundles

*-rawMagma : RawMagma 0ℓ 0ℓ
*-rawMagma = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  }

*-1-rawMonoid : RawMonoid 0ℓ 0ℓ
*-1-rawMonoid = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; ε = +
  }

*-1-rawGroup : RawGroup 0ℓ 0ℓ
*-1-rawGroup = record
  { _≈_ = _≡_
  ; _∙_ = _*_
  ; _⁻¹ = opposite
  ; ε = +
  }

