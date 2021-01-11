------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list appending
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary using (Setoid)

module Data.List.Relation.Ternary.Appending.Setoid.Properties {c l} (S : Setoid c l) where

open import Data.List.Base as List using (List; [])
import Data.List.Properties as Listₚ
open import Data.List.Relation.Binary.Pointwise using (Pointwise; [])
import Data.List.Relation.Ternary.Appending.Properties as Appendingₚ
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Data.List.Relation.Ternary.Appending.Setoid S
module S = Setoid S; open S renaming (Carrier to A) using (_≈_)

private
  variable
    as bs cs : List A

------------------------------------------------------------------------
-- Re-exporting existing properties

open Appendingₚ public
  hiding (respʳ-≋; respˡ-≋)

------------------------------------------------------------------------
-- Proving setoid-specific ones

[]++⁻¹ : Appending [] bs cs → Pointwise _≈_ bs cs
[]++⁻¹ ([]++ rs) = rs

++[]⁻¹ : Appending as [] cs → Pointwise _≈_ as cs
++[]⁻¹ {as} {cs} ls with break ls
... | cs₁ , cs₂ , refl , pw , []
  rewrite Listₚ.++-identityʳ cs₁
  = pw

respʳ-≋ : ∀ {cs′} → Appending as bs cs → Pointwise _≈_ cs cs′ →
          Appending as bs cs′
respʳ-≋ = Appendingₚ.respʳ-≋ S.trans S.trans

respˡ-≋ : ∀ {as′ bs′} → Pointwise _≈_ as′ as → Pointwise _≈_ bs′ bs →
          Appending as bs cs → Appending as′ bs′ cs
respˡ-≋ = Appendingₚ.respˡ-≋ S.trans S.trans
