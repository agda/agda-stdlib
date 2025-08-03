------------------------------------------------------------------------
-- The Agda standard library
--
-- Some derivable properties
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Algebra.Bundles using (IdempotentCommutativeMonoid)

module Algebra.Properties.IdempotentCommutativeMonoid
  {c ℓ} (idempotentCommutativeMonoid : IdempotentCommutativeMonoid c ℓ) where

open IdempotentCommutativeMonoid idempotentCommutativeMonoid

open import Algebra.Consequences.Setoid setoid
  using (comm∧distrˡ⇒distrʳ; comm∧distrˡ⇒distr)
open import Algebra.Definitions _≈_
  using (_DistributesOverˡ_; _DistributesOverʳ_; _DistributesOver_)
open import Algebra.Properties.CommutativeSemigroup commutativeSemigroup
  using (medial)
open import Relation.Binary.Reasoning.Setoid setoid


------------------------------------------------------------------------
-- Distributivity

∙-distrˡ-∙ : _∙_ DistributesOverˡ _∙_
∙-distrˡ-∙ a b c = begin
    a ∙ (b ∙ c)        ≈⟨ ∙-congʳ (idem a) ⟨
    (a ∙ a) ∙ (b ∙ c)  ≈⟨ medial _ _ _ _ ⟩
    (a ∙ b) ∙ (a ∙ c)  ∎

∙-distrʳ-∙ : _∙_ DistributesOverʳ _∙_
∙-distrʳ-∙ = comm∧distrˡ⇒distrʳ ∙-cong comm ∙-distrˡ-∙

∙-distr-∙ : _∙_ DistributesOver _∙_
∙-distr-∙ = comm∧distrˡ⇒distr ∙-cong comm ∙-distrˡ-∙
