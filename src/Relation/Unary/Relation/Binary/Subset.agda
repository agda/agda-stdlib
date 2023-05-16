------------------------------------------------------------------------
-- The Agda standard library
--
-- Order properties of the subset relations _⊆_ and _⊂_
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Unary.Relation.Binary.Subset where

open import Level using (Level)
import Relation.Binary.Structures as BinaryStructures
open import Relation.Binary.Bundles
open import Relation.Unary
open import Relation.Unary.Properties
open import Relation.Unary.Relation.Binary.Equality using (≐-isEquivalence; ≐′-isEquivalence)

----------------------------------------------------------------------
-- Structures

module _ {a : Level} {A : Set a} {ℓ : Level} where

  open BinaryStructures {A = Pred A ℓ} _≐_

  ⊆-isPreorder : IsPreorder _⊆_
  ⊆-isPreorder = record
    { isEquivalence = ≐-isEquivalence
    ; reflexive = ⊆-reflexive
    ; trans = ⊆-trans
    }

  ⊆-isPartialOrder : IsPartialOrder _⊆_
  ⊆-isPartialOrder = record
    { isPreorder = ⊆-isPreorder
    ; antisym = ⊆-antisym
    }

  ⊂-isStrictPartialOrder : IsStrictPartialOrder _⊂_
  ⊂-isStrictPartialOrder = record
    { isEquivalence = ≐-isEquivalence
    ; irrefl = ⊂-irrefl
    ; trans = ⊂-trans
    ; <-resp-≈ = ⊂-resp-≐
    }

module _ {a : Level} {A : Set a} {ℓ : Level} where

  open BinaryStructures {A = Pred A ℓ} _≐′_

  ⊆′-isPreorder : IsPreorder _⊆′_
  ⊆′-isPreorder = record
    { isEquivalence = ≐′-isEquivalence
    ; reflexive = ⊆′-reflexive
    ; trans = ⊆′-trans
    }

  ⊆′-isPartialOrder : IsPartialOrder _⊆′_
  ⊆′-isPartialOrder = record
    { isPreorder = ⊆′-isPreorder
    ; antisym = ⊆′-antisym
    }

  ⊂′-isStrictPartialOrder : IsStrictPartialOrder _⊂′_
  ⊂′-isStrictPartialOrder = record
    { isEquivalence = ≐′-isEquivalence
    ; irrefl = ⊂′-irrefl
    ; trans = ⊂′-trans
    ; <-resp-≈ = ⊂′-resp-≐′
    }

----------------------------------------------------------------------
-- Bundles

module _ {a : Level} (A : Set a) (ℓ : Level) where

  ⊆-preorder : Preorder _ _ _
  ⊆-preorder = record
    { isPreorder = ⊆-isPreorder {A = A} {ℓ}
    }

  ⊆-poset : Poset _ _ _
  ⊆-poset = record
    { isPartialOrder = ⊆-isPartialOrder {A = A} {ℓ}
    }

  ⊂-strictPartialOrder : StrictPartialOrder _ _ _
  ⊂-strictPartialOrder = record
    { isStrictPartialOrder = ⊂-isStrictPartialOrder {A = A} {ℓ}
    }

  ⊆′-preorder : Preorder _ _ _
  ⊆′-preorder = record
    { isPreorder = ⊆′-isPreorder {A = A} {ℓ}
    }

  ⊆′-poset : Poset _ _ _
  ⊆′-poset = record
    { isPartialOrder = ⊆′-isPartialOrder {A = A} {ℓ}
    }

  ⊂′-strictPartialOrder : StrictPartialOrder _ _ _
  ⊂′-strictPartialOrder = record
    { isStrictPartialOrder = ⊂′-isStrictPartialOrder {A = A} {ℓ}
    }
