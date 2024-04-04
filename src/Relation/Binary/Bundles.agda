------------------------------------------------------------------------
-- The Agda standard library
--
-- Bundles for homogeneous binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Bundles where

open import Function.Base using (flip)
open import Level using (Level; suc; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures -- most of it

------------------------------------------------------------------------
-- Setoids
------------------------------------------------------------------------

record PartialSetoid a ℓ : Set (suc (a ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier              : Set a
    _≈_                  : Rel Carrier ℓ
    isPartialEquivalence : IsPartialEquivalence _≈_

  open IsPartialEquivalence isPartialEquivalence public

  infix 4 _≉_
  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)


record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public
    using (refl; reflexive; isPartialEquivalence)

  partialSetoid : PartialSetoid c ℓ
  partialSetoid = record
    { isPartialEquivalence = isPartialEquivalence
    }

  open PartialSetoid partialSetoid public
    hiding (Carrier; _≈_; isPartialEquivalence)


record DecSetoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public
    using (_≟_; isEquivalence)

  setoid : Setoid c ℓ
  setoid = record
    { isEquivalence = isEquivalence
    }

  open Setoid setoid public
    hiding (Carrier; _≈_; isEquivalence)

------------------------------------------------------------------------
-- Preorders
------------------------------------------------------------------------

record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≲_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _≲_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _≲_

  open IsPreorder isPreorder public
    hiding (module Eq)

  module Eq where
    setoid : Setoid c ℓ₁
    setoid = record
      { isEquivalence = isEquivalence
      }

    open Setoid setoid public

  infix 4 _⋦_
  _⋦_ : Rel Carrier _
  x ⋦ y = ¬ (x ≲ y)

  infix 4 _≳_
  _≳_ = flip _≲_

  infix 4 _⋧_
  _⋧_ = flip _⋦_

  -- Deprecated.
  infix 4 _∼_
  _∼_ = _≲_
  {-# WARNING_ON_USAGE _∼_
  "Warning: _∼_ was deprecated in v2.0.
  Please use _≲_ instead. "
  #-}


record TotalPreorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≲_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁  -- The underlying equality.
    _≲_             : Rel Carrier ℓ₂  -- The relation.
    isTotalPreorder : IsTotalPreorder _≈_ _≲_

  open IsTotalPreorder isTotalPreorder public
    using (total; isPreorder)

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record
    { isPreorder = isPreorder
    }

  open Preorder preorder public
    hiding (Carrier; _≈_; _≲_; isPreorder)

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
    using (antisym; isPreorder)

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record
    { isPreorder = isPreorder
    }

  open Preorder preorder public
    hiding (Carrier; _≈_; _≲_; isPreorder)
    renaming
    ( _⋦_ to _≰_; _≳_ to _≥_; _⋧_ to _≱_
    ; ≲-respˡ-≈ to ≤-respˡ-≈
    ; ≲-respʳ-≈ to ≤-respʳ-≈
    ; ≲-resp-≈  to ≤-resp-≈
    )


record DecPoset c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ₁
    _≤_               : Rel Carrier ℓ₂
    isDecPartialOrder : IsDecPartialOrder _≈_ _≤_

  private module DPO = IsDecPartialOrder isDecPartialOrder

  open DPO public
    using (_≟_; _≤?_; isPartialOrder)

  poset : Poset c ℓ₁ ℓ₂
  poset = record
    { isPartialOrder = isPartialOrder
    }

  open Poset poset public
    hiding (Carrier; _≈_; _≤_; isPartialOrder; module Eq)

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

  infix 4 _≮_
  _≮_ : Rel Carrier _
  x ≮ y = ¬ (x < y)

  infix 4 _>_
  _>_ = flip _<_

  infix 4 _≯_
  _≯_ = flip _≮_


record DecStrictPartialOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier                 : Set c
    _≈_                     : Rel Carrier ℓ₁
    _<_                     : Rel Carrier ℓ₂
    isDecStrictPartialOrder : IsDecStrictPartialOrder _≈_ _<_

  private module DSPO = IsDecStrictPartialOrder isDecStrictPartialOrder

  open DSPO public
    using (_<?_; _≟_; isStrictPartialOrder)

  strictPartialOrder : StrictPartialOrder c ℓ₁ ℓ₂
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }

  open StrictPartialOrder strictPartialOrder public
    hiding (Carrier; _≈_; _<_; isStrictPartialOrder; module Eq)

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
    using (total; isPartialOrder; isTotalPreorder)

  poset : Poset c ℓ₁ ℓ₂
  poset = record
    { isPartialOrder = isPartialOrder
    }

  open Poset poset public
    hiding (Carrier; _≈_; _≤_; isPartialOrder)

  totalPreorder : TotalPreorder c ℓ₁ ℓ₂
  totalPreorder = record
    { isTotalPreorder = isTotalPreorder
    }


record DecTotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _≤_             : Rel Carrier ℓ₂
    isDecTotalOrder : IsDecTotalOrder _≈_ _≤_

  private module DTO = IsDecTotalOrder isDecTotalOrder

  open DTO public
    using (_≟_; _≤?_; isTotalOrder; isDecPartialOrder)

  totalOrder : TotalOrder c ℓ₁ ℓ₂
  totalOrder = record
    { isTotalOrder = isTotalOrder
    }

  open TotalOrder totalOrder public
    hiding (Carrier; _≈_; _≤_; isTotalOrder; module Eq)

  decPoset : DecPoset c ℓ₁ ℓ₂
  decPoset = record
    { isDecPartialOrder = isDecPartialOrder
    }

  open DecPoset decPoset public
    using (module Eq)


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
    using
    ( _≟_; _<?_; compare; isStrictPartialOrder
    ; isDecStrictPartialOrder; isDecEquivalence
    )

  strictPartialOrder : StrictPartialOrder c ℓ₁ ℓ₂
  strictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    }

  open StrictPartialOrder strictPartialOrder public
    hiding (Carrier; _≈_; _<_; isStrictPartialOrder; module Eq)

  decStrictPartialOrder : DecStrictPartialOrder c ℓ₁ ℓ₂
  decStrictPartialOrder = record
    { isDecStrictPartialOrder = isDecStrictPartialOrder
    }

  open DecStrictPartialOrder decStrictPartialOrder public
    using (module Eq)

  decSetoid : DecSetoid c ℓ₁
  decSetoid = record
    { isDecEquivalence = Eq.isDecEquivalence
    }
  {-# WARNING_ON_USAGE decSetoid
  "Warning: decSetoid was deprecated in v1.3.
  Please use Eq.decSetoid instead."
  #-}


record DenseLinearOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier            : Set c
    _≈_                : Rel Carrier ℓ₁
    _<_                : Rel Carrier ℓ₂
    isDenseLinearOrder : IsDenseLinearOrder _≈_ _<_

  open IsDenseLinearOrder isDenseLinearOrder public
    using (isStrictTotalOrder; dense)

  strictTotalOrder : StrictTotalOrder c ℓ₁ ℓ₂
  strictTotalOrder = record
    { isStrictTotalOrder = isStrictTotalOrder
    }

  open StrictTotalOrder strictTotalOrder public
    hiding (Carrier; _≈_; _<_; isStrictTotalOrder)


------------------------------------------------------------------------
-- Apartness relations
------------------------------------------------------------------------

record ApartnessRelation c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _#_
  field
    Carrier             : Set c
    _≈_                 : Rel Carrier ℓ₁
    _#_                 : Rel Carrier ℓ₂
    isApartnessRelation : IsApartnessRelation _≈_ _#_

  open IsApartnessRelation isApartnessRelation public
