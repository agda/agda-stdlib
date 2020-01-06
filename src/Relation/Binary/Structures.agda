------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for homogeneous binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --without-K --safe #-}

open import Relation.Binary.Core

module Relation.Binary.Structures
  {a ℓ} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ)   -- The underlying equality relation
  where

open import Data.Product using (proj₁; proj₂; _,_)
open import Level using (Level; _⊔_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality.Core as P using (_≡_)
open import Relation.Binary.Consequences
open import Relation.Binary.Definitions

private
  variable
    ℓ₂ : Level

------------------------------------------------------------------------
-- Equivalences
------------------------------------------------------------------------
-- Note all the following equivalences refer to the equality provided
-- as a module parameter at the top of this file.

record IsPartialEquivalence : Set (a ⊔ ℓ) where
  field
    sym   : Symmetric _≈_
    trans : Transitive _≈_

-- The preorders of this library are defined in terms of an underlying
-- equivalence relation, and hence equivalence relations are not
-- defined in terms of preorders.

-- To preserve backwards compatability, equivalence relations are
-- not defined in terms of their partial counterparts.

record IsEquivalence : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  reflexive : _≡_ ⇒ _≈_
  reflexive P.refl = refl

  isPartialEquivalence : IsPartialEquivalence
  isPartialEquivalence = record
    { sym = sym
    ; trans = trans
    }


record IsDecEquivalence : Set (a ⊔ ℓ) where
  infix 4 _≟_
  field
    isEquivalence : IsEquivalence
    _≟_           : Decidable _≈_

  open IsEquivalence isEquivalence public


------------------------------------------------------------------------
-- Preorders
------------------------------------------------------------------------

record IsPreorder (_∼_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence
    -- Reflexivity is expressed in terms of the underlying equality:
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

------------------------------------------------------------------------
-- Partial orders
------------------------------------------------------------------------

record IsPartialOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≤_
    antisym    : Antisymmetric _≈_ _≤_

  open IsPreorder isPreorder public
    renaming
    ( ∼-respˡ-≈ to ≤-respˡ-≈
    ; ∼-respʳ-≈ to ≤-respʳ-≈
    ; ∼-resp-≈  to ≤-resp-≈
    )


record IsDecPartialOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_
  field
    isPartialOrder : IsPartialOrder _≤_
    _≟_            : Decidable _≈_
    _≤?_           : Decidable _≤_

  open IsPartialOrder isPartialOrder public
    hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence
    isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public


record IsStrictPartialOrder (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence
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


record IsDecStrictPartialOrder (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  infix 4 _≟_ _<?_
  field
    isStrictPartialOrder : IsStrictPartialOrder _<_
    _≟_                  : Decidable _≈_
    _<?_                 : Decidable _<_

  private
    module SPO = IsStrictPartialOrder isStrictPartialOrder

  open SPO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence
    isDecEquivalence = record
      { isEquivalence = SPO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public


------------------------------------------------------------------------
-- Total orders
------------------------------------------------------------------------

record IsTotalOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≤_
    total          : Total _≤_

  open IsPartialOrder isPartialOrder public


record IsDecTotalOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_
  field
    isTotalOrder : IsTotalOrder _≤_
    _≟_          : Decidable _≈_
    _≤?_         : Decidable _≤_

  open IsTotalOrder isTotalOrder public
    hiding (module Eq)

  isDecPartialOrder : IsDecPartialOrder _≤_
  isDecPartialOrder = record
    { isPartialOrder = isPartialOrder
    ; _≟_            = _≟_
    ; _≤?_           = _≤?_
    }

  module Eq where

    isDecEquivalence : IsDecEquivalence
    isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public


-- Note that these orders are decidable. The current implementation
-- of `Trichotomous` subsumes irreflexivity and asymmetry. Any reasonable
-- definition capturing these three properties implies decidability
-- as `Trichotomous` necessarily separates out the equality case.

record IsStrictTotalOrder (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence
    trans         : Transitive _<_
    compare       : Trichotomous _≈_ _<_

  infix 4 _≟_ _<?_

  _≟_ : Decidable _≈_
  _≟_ = tri⟶dec≈ compare

  _<?_ : Decidable _<_
  _<?_ = tri⟶dec< compare

  isDecEquivalence : IsDecEquivalence
  isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_           = _≟_
    }

  module Eq = IsDecEquivalence isDecEquivalence

  isStrictPartialOrder : IsStrictPartialOrder _<_
  isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl        = tri⟶irr compare
    ; trans         = trans
    ; <-resp-≈      = trans∧tri⟶resp≈ Eq.sym Eq.trans trans compare
    }

  isDecStrictPartialOrder : IsDecStrictPartialOrder _<_
  isDecStrictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    ; _≟_                  = _≟_
    ; _<?_                 = _<?_
    }

  open IsStrictPartialOrder isStrictPartialOrder public
    using (irrefl; asym; <-respʳ-≈; <-respˡ-≈; <-resp-≈)
