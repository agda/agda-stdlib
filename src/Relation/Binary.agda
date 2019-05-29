------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Product
open import Data.Sum
open import Function.Core
open import Level
open import Relation.Nullary using (¬_)
import Relation.Binary.PropositionalEquality.Core as PropEq
open import Relation.Binary.Consequences

------------------------------------------------------------------------
-- Simple properties and equivalence relations

open import Relation.Binary.Core public

------------------------------------------------------------------------
-- Preorders

record IsPreorder {a ℓ₁ ℓ₂} {A : Set a}
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    -- Reflexivity is expressed in terms of an underlying equality:
    reflexive     : _≈_ ⇒ _∼_
    trans         : Transitive _∼_

  module Eq = IsEquivalence isEquivalence

  refl : Reflexive _∼_
  refl = reflexive Eq.refl

  ∼-respˡ-≈ : _∼_ Respectsˡ _≈_
  ∼-respˡ-≈ x≈y x∼z = trans (reflexive (Eq.sym x≈y)) x∼z

  ∼-respʳ-≈ : _∼_ Respectsʳ _≈_
  ∼-respʳ-≈ x≈y z∼x = trans z∼x (reflexive x≈y)

  ∼-resp-≈ : _∼_ Respects₂ _≈_
  ∼-resp-≈ = ∼-respʳ-≈ , ∼-respˡ-≈

record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  open IsPreorder isPreorder public

------------------------------------------------------------------------
-- Setoids

-- Equivalence relations are defined in Relation.Binary.Core.

record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  _≉_ : Rel Carrier _
  x ≉ y = ¬ (x ≈ y)

  open IsEquivalence isEquivalence public

  isPreorder : IsPreorder _≡_ _≈_
  isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }

  preorder : Preorder c c ℓ
  preorder = record { isPreorder = isPreorder }

------------------------------------------------------------------------
-- Decidable equivalence relations

record IsDecEquivalence {a ℓ} {A : Set a}
                        (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  infix 4 _≟_
  field
    isEquivalence : IsEquivalence _≈_
    _≟_           : Decidable _≈_

  open IsEquivalence isEquivalence public

record DecSetoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public

  setoid : Setoid c ℓ
  setoid = record { isEquivalence = isEquivalence }

  open Setoid setoid public using (preorder)

------------------------------------------------------------------------
-- Partial orders

record IsPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                      (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                      Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≈_ _≤_
    antisym    : Antisymmetric _≈_ _≤_

  open IsPreorder isPreorder public
    renaming
    ( ∼-respˡ-≈ to ≤-respˡ-≈
    ; ∼-respʳ-≈ to ≤-respʳ-≈
    ; ∼-resp-≈  to ≤-resp-≈
    )

record Poset c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁
    _≤_            : Rel Carrier ℓ₂
    isPartialOrder : IsPartialOrder _≈_ _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }

------------------------------------------------------------------------
-- Decidable partial orders

record IsDecPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                         (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                         Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    _≟_            : Decidable _≈_
    _≤?_           : Decidable _≤_

  private
    module PO = IsPartialOrder isPartialOrder
  open PO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = PO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public

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
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record { isDecEquivalence = DPO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public

------------------------------------------------------------------------
-- Strict partial orders

record IsStrictPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                            (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) :
                            Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    irrefl        : Irreflexive _≈_ _<_
    trans         : Transitive _<_
    <-resp-≈      : _<_ Respects₂ _≈_

  module Eq = IsEquivalence isEquivalence

  asym : Asymmetric _<_
  asym {x} {y} = trans∧irr⟶asym Eq.refl trans irrefl {x = x} {y}

  <-respʳ-≈ : _<_ Respectsʳ _≈_
  <-respʳ-≈ = proj₁ <-resp-≈

  <-respˡ-≈ : _<_ Respectsˡ _≈_
  <-respˡ-≈ = proj₂ <-resp-≈

  asymmetric = asym
  {-# WARNING_ON_USAGE asymmetric
  "Warning: asymmetric was deprecated in v0.16.
  Please use asym instead."
  #-}

record StrictPartialOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ₁
    _<_                  : Rel Carrier ℓ₂
    isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_

  open IsStrictPartialOrder isStrictPartialOrder public

------------------------------------------------------------------------
-- Decidable strict partial orders

record IsDecStrictPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                               (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) :
                               Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infix 4 _≟_ _<?_
  field
    isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_
    _≟_                  : Decidable _≈_
    _<?_                 : Decidable _<_

  private
    module SPO = IsStrictPartialOrder isStrictPartialOrder
    open SPO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = SPO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public

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
  strictPartialOrder = record { isStrictPartialOrder = isStrictPartialOrder }

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record { isDecEquivalence = DSPO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public

------------------------------------------------------------------------
-- Total orders

record IsTotalOrder {a ℓ₁ ℓ₂} {A : Set a}
                    (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                    Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    total          : Total _≤_

  open IsPartialOrder isPartialOrder public

record TotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier      : Set c
    _≈_          : Rel Carrier ℓ₁
    _≤_          : Rel Carrier ℓ₂
    isTotalOrder : IsTotalOrder _≈_ _≤_

  open IsTotalOrder isTotalOrder public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

------------------------------------------------------------------------
-- Decidable total orders

record IsDecTotalOrder {a ℓ₁ ℓ₂} {A : Set a}
                       (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                       Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_
  field
    isTotalOrder : IsTotalOrder _≈_ _≤_
    _≟_          : Decidable _≈_
    _≤?_         : Decidable _≤_

  open IsTotalOrder isTotalOrder public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public

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
  totalOrder = record { isTotalOrder = isTotalOrder }

  open TotalOrder totalOrder public using (poset; preorder)

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record { isDecEquivalence = DTO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public

------------------------------------------------------------------------
-- Strict total orders

-- Note that these orders are decidable. The current implementation
-- of `Trichotomous` subsumes irreflexivity and asymmetry. Any reasonable
-- definition capturing these three properties implies decidability
-- as `Trichotomous` necessarily separates out the equality case.

record IsStrictTotalOrder {a ℓ₁ ℓ₂} {A : Set a}
                          (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) :
                          Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    trans         : Transitive _<_
    compare       : Trichotomous _≈_ _<_

  infix 4 _≟_ _<?_

  _≟_ : Decidable _≈_
  _≟_ = tri⟶dec≈ compare

  _<?_ : Decidable _<_
  _<?_ = tri⟶dec< compare

  isDecEquivalence : IsDecEquivalence _≈_
  isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_           = _≟_
    }

  module Eq = IsDecEquivalence isDecEquivalence

  <-respˡ-≈ : _<_ Respectsˡ _≈_
  <-respˡ-≈ = trans∧tri⟶respˡ≈ Eq.trans trans compare

  <-respʳ-≈ : _<_ Respectsʳ _≈_
  <-respʳ-≈ = trans∧tri⟶respʳ≈ Eq.sym Eq.trans trans compare

  <-resp-≈ : _<_ Respects₂ _≈_
  <-resp-≈ = <-respʳ-≈ , <-respˡ-≈

  isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_
  isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl        = tri⟶irr compare
    ; trans         = trans
    ; <-resp-≈      = <-resp-≈
    }

  open IsStrictPartialOrder isStrictPartialOrder public
    using (irrefl; asym)

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
  strictPartialOrder =
    record { isStrictPartialOrder = isStrictPartialOrder }

  decSetoid : DecSetoid c ℓ₁
  decSetoid = record { isDecEquivalence = isDecEquivalence }

  module Eq = DecSetoid decSetoid
