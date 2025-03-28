------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed M-types (the dual of indexed W-types aka Petersson-Synek
-- trees).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe --guardedness #-}

module Codata.Musical.M.Indexed where

open import Level using (Level; _⊔_)
open import Codata.Musical.Notation using (♭; ∞; ♯_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Container.Indexed.Core
open import Function.Base using (_∘_)
open import Relation.Unary using (Pred; _⊆_)

-- The family of indexed M-types.

module _ {ℓ c r} {O : Set ℓ} (C : Container O O c r) where

  data M (o : O) : Set (ℓ ⊔ c ⊔ r) where
    inf : ⟦ C ⟧ (∞ ∘ M) o → M o

  open Container C

  -- Projections.

  head : M ⊆ Command
  head (inf (c , _)) = c

  tail : ∀ {o} (m : M o) (r : Response (head m)) → M (next (head m) r)
  tail (inf (_ , k)) r = ♭ (k r)

  force : M ⊆ ⟦ C ⟧ M
  force (inf (c , k)) = c , λ r → ♭ (k r)

  -- Coiteration.

  coit : ∀ {ℓ} {X : Pred O ℓ} → X ⊆ ⟦ C ⟧ X → X ⊆ M
  coit ψ x = inf (proj₁ cs , λ r → ♯ coit ψ (proj₂ cs r))
    where
    cs = ψ x
