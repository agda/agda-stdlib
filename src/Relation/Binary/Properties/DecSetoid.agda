------------------------------------------------------------------------
-- The Agda standard library
--
-- Every decidable setoid induces tight apartness relation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (DecSetoid; ApartnessRelation)

module Relation.Binary.Properties.DecSetoid {c ℓ} (S : DecSetoid c ℓ) where

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.Definitions
  using (Cotransitive; Tight)
import Relation.Binary.Properties.Setoid as SetoidProperties
open import Relation.Binary.Structures
  using (IsApartnessRelation; IsDecEquivalence)
open import Relation.Nullary.Decidable.Core
  using (yes; no; decidable-stable)

open DecSetoid S using (_≈_; _≉_; _≟_; setoid; trans)
open SetoidProperties setoid

≉-cotrans : Cotransitive _≉_
≉-cotrans {x} {y} x≉y z with x ≟ z | z ≟ y
... | _ | no z≉y = inj₂ z≉y
... | no x≉z | _ = inj₁ x≉z
... | yes x≈z | yes z≈y = inj₁ λ _ → x≉y (trans x≈z z≈y)

≉-isApartnessRelation : IsApartnessRelation _≈_ _≉_
≉-isApartnessRelation = record
  { irrefl = ≉-irrefl
  ; sym = ≉-sym
  ; cotrans = ≉-cotrans
  }

≉-apartnessRelation : ApartnessRelation c ℓ ℓ
≉-apartnessRelation = record { isApartnessRelation = ≉-isApartnessRelation }

≉-tight : Tight _≈_ _≉_
≉-tight x y = decidable-stable (x ≟ y) , ≉-irrefl
