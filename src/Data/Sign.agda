------------------------------------------------------------------------
-- The Agda standard library
--
-- Signs
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sign where

open import Relation.Binary using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

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
-- Decidable equality.

infix 4 _≟_

_≟_ : Decidable {A = Sign} _≡_
- ≟ - = yes refl
- ≟ + = no λ()
+ ≟ - = no λ()
+ ≟ + = yes refl

