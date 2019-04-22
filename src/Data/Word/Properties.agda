------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of operations on machine words
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Word.Properties where

open import Data.Bool.Base using (Bool)
open import Data.Word.Base
import Data.Nat.Properties as ℕₚ
open import Function
open import Relation.Nullary.Decidable using (map′; ⌊_⌋)
open import Relation.Binary
  using (Decidable; Setoid; DecSetoid; StrictTotalOrder)
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; cong)

------------------------------------------------------------------------
-- Primitive properties

open import Agda.Builtin.Word.Properties
  renaming (primWord64ToNatInjective to toℕ-injective)
  public

------------------------------------------------------------------------
-- Decidable equality

infix 4 _≟_
_≟_ : Decidable {A = Word64} _≡_
x ≟ y = map′ (toℕ-injective x y) (cong toℕ) (toℕ x ℕₚ.≟ toℕ y)

------------------------------------------------------------------------
-- Boolean equality test.

infix 4 _==_
_==_ : Word64 → Word64 → Bool
w₁ == w₂ = ⌊ w₁ ≟ w₂ ⌋

------------------------------------------------------------------------
-- Structures

setoid : Setoid _ _
setoid = P.setoid Word64

decSetoid : DecSetoid _ _
decSetoid = P.decSetoid _≟_

strictTotalOrder : StrictTotalOrder _ _ _
strictTotalOrder = On.strictTotalOrder ℕₚ.<-strictTotalOrder toℕ
