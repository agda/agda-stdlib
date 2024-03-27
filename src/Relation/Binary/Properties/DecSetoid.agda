------------------------------------------------------------------------
-- The Agda standard library
--
-- Every decidable setoid induces tight apartness relation.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary using (DecSetoid)

module Relation.Binary.Properties.DecSetoid {c ℓ} (S : DecSetoid c ℓ) where

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Relation.Binary.Definitions
  using (Cotransitive; Tight)

open import Relation.Binary
  using (IsApartnessRelation; ApartnessRelation; IsDecEquivalence)

open DecSetoid S using (_≈_; _≉_; isDecEquivalence; Carrier; setoid)
open IsDecEquivalence isDecEquivalence

open import Relation.Binary.Properties.Setoid setoid

≉-cotrans : Cotransitive _≉_
≉-cotrans {x} {y} x≉y z with x ≟ z | z ≟ y
≉-cotrans {x} {y} x≉y z | _ | no z≉y = inj₂ z≉y
≉-cotrans {x} {y} x≉y z | no x≉z | _ = inj₁ x≉z
≉-cotrans {x} {y} x≉y z | yes x≈z | yes z≈y = inj₁ λ _ → x≉y (trans x≈z z≈y)

≉-isApartnessRelation : IsApartnessRelation _≈_ _≉_
≉-isApartnessRelation =
  record
  { irrefl = ≉-irrefl
  ; sym = ≉-sym
  ; cotrans = ≉-cotrans
  }

≉-apartnessRelation : ApartnessRelation c ℓ ℓ
≉-apartnessRelation = record { isApartnessRelation = ≉-isApartnessRelation }

≉-tight : Tight _≈_ _≉_
≉-tight x y = decidable-stable (x ≟ y) , ≉-irrefl
