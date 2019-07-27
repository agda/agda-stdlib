------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple predicates over ℕ
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Integer.Predicate where

open import Data.Integer.Base
open import Data.Integer.Properties
open import Data.Nat as ℕ using (z≤n; s≤s)
open import Level using (0ℓ)
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality using (_≢_; refl)
open import Relation.Unary using (Pred)

------------------------------------------------------------------------
-- Definition

-- The predicates here are defined in a slight odd manner. Instead of
-- defining `NonZero x` as `x ≢ +0` or via a datatype as might be
-- expected we define it in terms of `False` and the decidability of
-- propositional equality `_≟_`. This ensures that for any `x` of the
-- form `-[1+ y ]` then Agda can automatically infer `NonZero x` and
-- hence when it is passed as an implicit argument no proof is required.
-- See `Data.Integer.DivMod` for an example.

NonZero : Pred ℤ 0ℓ
NonZero i = False (∣ i ∣ ℕ.≟ 0)

Positive : Pred ℤ 0ℓ
Positive i = True (+0 <? i)

Negative : Pred ℤ 0ℓ
Negative i = True (i <? +0)

NonPositive : Pred ℤ 0ℓ
NonPositive i = True (i ≤? +0)

NonNegative : Pred ℤ 0ℓ
NonNegative i = True (+0 ≤? i)

------------------------------------------------------------------------
-- Constructors

nonZero : ∀ {i} → i ≢ +0 → NonZero i
nonZero { +[1+ n ]} i≢0 = _
nonZero { +0}       i≢0 = i≢0 refl
nonZero { -[1+ n ]} i≢0 = _

positive : ∀ {i} → +0 < i → Positive i
positive (+<+ (s≤s m<n)) = _

negative : ∀ {i} → i < +0 → Negative i
negative -<+ = _

nonPositive : ∀ {i} → i ≤ +0 → NonPositive i
nonPositive -≤+       = _
nonPositive (+≤+ z≤n) = _

nonNegative : ∀ {i} → +0 ≤ i → NonNegative i
nonNegative (+≤+ z≤n) = _
