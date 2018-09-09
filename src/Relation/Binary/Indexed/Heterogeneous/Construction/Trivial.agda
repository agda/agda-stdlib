------------------------------------------------------------------------
-- The Agda standard library
--
-- Takes a binary relation structures to their trivialy indexed
-- counterparts.
------------------------------------------------------------------------

open import Relation.Binary
open import Relation.Binary.Indexed.Heterogeneous hiding (Rel)
  hiding (IsEquivalence; Setoid)

module Relation.Binary.Indexed.Heterogeneous.Construction.Trivial
  {i} {I : Set i} where

------------------------------------------------------------------------
-- Structures

module _ {a} {A : Set a} where

  private
    Aᵢ : I → Set a
    Aᵢ i = A

  isIndexedEquivalence : ∀ {ℓ} {_≈_ : Rel A ℓ} → IsEquivalence _≈_ →
                         IsIndexedEquivalence Aᵢ _≈_
  isIndexedEquivalence isEq = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
    where open IsEquivalence isEq

  isIndexedPreorder : ∀ {ℓ₁ ℓ₂} {_≈_ : Rel A ℓ₁} {_∼_ : Rel A ℓ₂} →
                      IsPreorder _≈_ _∼_ →
                      IsIndexedPreorder Aᵢ _≈_ _∼_
  isIndexedPreorder isPreorder = record
    { isEquivalence = isIndexedEquivalence isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }
    where open IsPreorder isPreorder

------------------------------------------------------------------------
-- Packages

indexedSetoid : ∀ {a ℓ} → Setoid a ℓ → IndexedSetoid I a ℓ
indexedSetoid S = record
  { isEquivalence = isIndexedEquivalence isEquivalence
  }
  where open Setoid S

indexedPreorder : ∀ {a ℓ₁ ℓ₂} → Preorder a ℓ₁ ℓ₂ →
                  IndexedPreorder I a ℓ₁ ℓ₂
indexedPreorder O = record
  { isPreorder = isIndexedPreorder isPreorder
  }
  where open Preorder O
