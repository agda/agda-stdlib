------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed W-types aka Petersson-Synek trees
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.W.Indexed where

open import Level using (Level; _⊔_)
open import Data.Container.Indexed.Core using (Container; ⟦_⟧; □)
open import Data.Product.Base using (_,_; Σ)
open import Relation.Unary using (Pred; _⊆_; _∩_; _∪_)

-- The family of indexed W-types.

module _ {ℓ c r} {O : Set ℓ} (C : Container O O c r) where

  open Container C

  data W (o : O) : Set (ℓ ⊔ c ⊔ r) where
    sup : ⟦ C ⟧ W o → W o

  -- Projections.

  head : W ⊆ Command
  head (sup (c , _)) = c

  tail : ∀ {o} (w : W o) (r : Response (head w)) → W (next (head w) r)
  tail (sup (_ , k)) r = k r

  -- Induction, (primitive) recursion and iteration.

  ind : ∀ {ℓ} (P : Pred (Σ O W) ℓ) →
        (∀ {o} (cs : ⟦ C ⟧ W o) → □ C P (o , cs) → P (o , sup cs)) →
        ∀ {o} (w : W o) → P (o , w)
  ind P φ (sup (c , k)) = φ (c , k) (λ r → ind P φ (k r))

  rec : ∀ {ℓ} {X : Pred O ℓ} → (⟦ C ⟧ (W ∩ X) ⊆ X) → W ⊆ X
  rec φ (sup (c , k))= φ (c , λ r → (k r , rec φ (k r)))

  iter : ∀ {ℓ} {X : Pred O ℓ} → (⟦ C ⟧ X ⊆ X) → W ⊆ X
  iter φ (sup (c , k))= φ (c , λ r → iter φ (k r))
