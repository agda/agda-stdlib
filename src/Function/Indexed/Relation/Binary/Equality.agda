------------------------------------------------------------------------
-- The Agda standard library
--
-- Function setoids and related constructions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Function.Indexed.Relation.Binary.Equality where

open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.Indexed.Heterogeneous using (IndexedSetoid)

-- A variant of setoid which uses the propositional equality setoid
-- for the domain, and a more convenient definition of _≈_.

≡-setoid : ∀ {f t₁ t₂} (From : Set f) → IndexedSetoid From t₁ t₂ → Setoid _ _
≡-setoid From To = record
  { Carrier       = (x : From) → Carrier x
  ; _≈_           = λ f g → ∀ x → f x ≈ g x
  ; isEquivalence = record
    { refl  = λ {f} x → refl
    ; sym   = λ f∼g x → sym (f∼g x)
    ; trans = λ f∼g g∼h x → trans (f∼g x) (g∼h x)
    }
  } where open IndexedSetoid To

