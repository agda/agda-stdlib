------------------------------------------------------------------------
-- The Agda standard library
--
-- Core properties of Fin, lifted out to avoid dependency cycles
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Fin.Properties.Core where

open import Data.Fin.Base
open import Data.Fin.Patterns
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.Bundles
  using (Setoid; DecSetoid; Preorder)
open import Relation.Binary.Structures
  using (IsDecEquivalence)
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; cong)
import Relation.Binary.PropositionalEquality.Properties as ≡
open import Relation.Nullary.Decidable as Dec
  using (yes; no; map′)


private
  variable
    n : ℕ
    i j : Fin n

------------------------------------------------------------------------
-- Properties of _≡_
------------------------------------------------------------------------

0≢1+n : zero ≢ suc i
0≢1+n ()

suc-injective : suc i ≡ suc j → i ≡ j
suc-injective refl = refl

infix 4 _≟_

_≟_ : DecidableEquality (Fin n)
zero  ≟ zero  = yes refl
zero  ≟ suc y = no λ()
suc x ≟ zero  = no λ()
suc x ≟ suc y = map′ (cong suc) suc-injective (x ≟ y)

------------------------------------------------------------------------
-- Structures

≡-isDecEquivalence : IsDecEquivalence {A = Fin n} _≡_
≡-isDecEquivalence = record
  { isEquivalence = ≡.isEquivalence
  ; _≟_           = _≟_
  }

------------------------------------------------------------------------
-- Bundles

≡-preorder : ℕ → Preorder _ _ _
≡-preorder n = ≡.preorder (Fin n)

≡-setoid : ℕ → Setoid _ _
≡-setoid n = ≡.setoid (Fin n)

≡-decSetoid : ℕ → DecSetoid _ _
≡-decSetoid n = record
  { isDecEquivalence = ≡-isDecEquivalence {n}
  }

