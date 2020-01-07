------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for homogeneous binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Bundles where

open import Level
open import Relation.Nullary using (¬_)
open import Relation.Binary.Core
open import Relation.Binary.Definitions
open import Relation.Binary.Structures

------------------------------------------------------------------------
-- Setoids
------------------------------------------------------------------------

record PartialSetoid a ℓ : Set (suc (a ⊔ ℓ)) where
  field
    Carrier              : Set a
    _≈_                  : Rel Carrier ℓ
    isPartialEquivalence : IsPartialEquivalence _≈_

  open IsPartialEquivalence isPartialEquivalence public

  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)


record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  partialSetoid : PartialSetoid c ℓ
  partialSetoid = record
    { isPartialEquivalence = isPartialEquivalence
    }

  open PartialSetoid partialSetoid public using (_≉_)


record DecSetoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public

  setoid : Setoid c ℓ
  setoid = record
    { isEquivalence = isEquivalence
    }

  open Setoid setoid public using (partialSetoid; _≉_)


------------------------------------------------------------------------
-- Preorders
------------------------------------------------------------------------

record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  open IsPreorder isPreorder public
    hiding (module Eq)

  module Eq where
    setoid : Setoid c ℓ₁
    setoid = record
      { isEquivalence = isEquivalence
      }

    open Setoid setoid public

------------------------------------------------------------------------
-- Partial orders
------------------------------------------------------------------------

record Poset c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁
    _≤_            : Rel Carrier ℓ₂
    isPartialOrder : IsPartialOrder _≈_ _≤_

  open IsPartialOrder isPartialOrder public
    hiding (module Eq)

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record
    { isPreorder = isPreorder
    }

  open Preorder preorder public
    using (module Eq)


record DecPoset c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ₁
    _≤_               : Rel Carrier ℓ₂
    isDecPartialOrder : IsDecPartialOrder _≈_ _≤_

  private
    module DPO = IsDecPartialOrder isDecPartialOrder
  open DPO public hiding (module Eq)

  poset : Poset c ℓ₁ ℓ₂
  poset = record
    { isPartialOrder = isPartialOrder
    }

  open Poset poset public
    using (preorder)

  module Eq where
    decSetoid : DecSetoid c ℓ₁
    decSetoid = record
      { isDecEquivalence = DPO.Eq.isDecEquivalence
      }

    open DecSetoid decSetoid public


record StrictPartialOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ₁
    _<_                  : Rel Carrier ℓ₂
    isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_

  open IsStrictPartialOrder isStrictPartialOrder public
    hiding (module Eq)

  module Eq where
    setoid : Setoid c ℓ₁
    setoid = record
      { isEquivalence = isEquivalence
      }

    open Setoid setoid public


record DecStrictPartialOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier                 : Set c
    _≈_                     : Rel Carrier ℓ₁
    _<_                     : Rel Carrier ℓ₂
    isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_

  private
    module DSPO = IsDecStrictPartialOrder isDecStrictPartialOrder
  open DSPO public hiding (module Eq)

  strictPartialOrder : StrictPartialOrder c ℓ₁ ℓ₂
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record
      { isDecEquivalence = DSPO.Eq.isDecEquivalence
      }

    open DecSetoid decSetoid public


------------------------------------------------------------------------
-- Total orders
------------------------------------------------------------------------

record TotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier      : Set c
    _≈_          : Rel Carrier ℓ₁
    _≤_          : Rel Carrier ℓ₂
    isTotalOrder : IsTotalOrder _≈_ _≤_

  open IsTotalOrder isTotalOrder public
    hiding (module Eq)

  poset : Poset c ℓ₁ ℓ₂
  poset = record
    { isPartialOrder = isPartialOrder
    }

  open Poset poset public
    using (module Eq; preorder)


record DecTotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _≤_             : Rel Carrier ℓ₂
    isDecTotalOrder : IsDecTotalOrder _≈_ _≤_

  private
    module DTO = IsDecTotalOrder isDecTotalOrder
  open DTO public hiding (module Eq)

  totalOrder : TotalOrder c ℓ₁ ℓ₂
  totalOrder = record
    { isTotalOrder = isTotalOrder
    }

  open TotalOrder totalOrder public using (poset; preorder)

  decPoset : DecPoset c ℓ₁ ℓ₂
  decPoset = record
    { isDecPartialOrder = isDecPartialOrder
    }

  open DecPoset decPoset public using (module Eq)


-- Note that these orders are decidable. The current implementation
-- of `Trichotomous` subsumes irreflexivity and asymmetry. Any reasonable
-- definition capturing these three properties implies decidability
-- as `Trichotomous` necessarily separates out the equality case.

record StrictTotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier            : Set c
    _≈_                : Rel Carrier ℓ₁
    _<_                : Rel Carrier ℓ₂
    isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_

  open IsStrictTotalOrder isStrictTotalOrder public
    hiding (module Eq)

  strictPartialOrder : StrictPartialOrder c ℓ₁ ℓ₂
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }

  open StrictPartialOrder strictPartialOrder public
    using (module Eq)

  decSetoid : DecSetoid c ℓ₁
  decSetoid = record
    { isDecEquivalence = isDecEquivalence
    }
  {-# WARNING_ON_USAGE decSetoid
  "Warning: decSetoid was deprecated in v1.3.
  Please use Eq.decSetoid instead."
  #-}
