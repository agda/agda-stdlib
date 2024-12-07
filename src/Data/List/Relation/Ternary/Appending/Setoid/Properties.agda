------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of list appending
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Bundles using (Setoid)

module Data.List.Relation.Ternary.Appending.Setoid.Properties
  {c l} (S : Setoid c l)
  where

open import Data.List.Base as List using (List; [])
import Data.List.Properties as List
open import Data.List.Relation.Binary.Pointwise.Base using (Pointwise; [])
import Data.List.Relation.Ternary.Appending.Properties as Appendingₚ
open import Data.Product.Base using (∃-syntax; _×_; _,_)
open import Function.Base using (id)
open import Relation.Binary.Core using (_⇒_)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Binary.Construct.Composition using (_;_)

open Setoid S renaming (Carrier to A)
open import Relation.Binary.Properties.Setoid S using (≈;≈⇒≈; ≈⇒≈;≈)
open import Data.List.Relation.Ternary.Appending.Setoid S

private
  variable
    as bs cs ds : List A

------------------------------------------------------------------------
-- Re-exporting existing properties

open Appendingₚ public
  using (conicalˡ; conicalʳ)

------------------------------------------------------------------------
-- Proving setoid-specific ones

[]++⁻¹ : Appending [] bs cs → Pointwise _≈_ bs cs
[]++⁻¹ ([]++ rs) = rs

++[]⁻¹ : Appending as [] cs → Pointwise _≈_ as cs
++[]⁻¹ {as} {cs} ls with break ls
... | cs₁ , cs₂ , refl , pw , []
  rewrite List.++-identityʳ cs₁
  = pw

respʳ-≋ : ∀ {cs′} → Appending as bs cs → Pointwise _≈_ cs cs′ →
          Appending as bs cs′
respʳ-≋ = Appendingₚ.respʳ-≋ trans trans

respˡ-≋ : ∀ {as′ bs′} → Pointwise _≈_ as′ as → Pointwise _≈_ bs′ bs →
          Appending as bs cs → Appending as′ bs′ cs
respˡ-≋ = Appendingₚ.respˡ-≋ trans trans

through→ :
  ∃[ xs ] Pointwise _≈_ as xs × Appending xs bs cs →
  ∃[ ys ] Appending as bs ys × Pointwise _≈_ ys cs
through→ = Appendingₚ.through→ ≈⇒≈;≈ id

through← :
  ∃[ ys ] Appending as bs ys × Pointwise _≈_ ys cs →
  ∃[ xs ] Pointwise _≈_ as xs × Appending xs bs cs
through← = Appendingₚ.through← ≈;≈⇒≈ id

assoc→ :
  ∃[ xs ] Appending as bs xs × Appending xs cs ds →
  ∃[ ys ] Appending bs cs ys × Appending as ys ds
assoc→ = Appendingₚ.assoc→ ≈⇒≈;≈ id ≈;≈⇒≈
