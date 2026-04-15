------------------------------------------------------------------------
-- The Agda standard library
--
-- Structures for homogeneous binary relations
------------------------------------------------------------------------

-- The contents of this module should be accessed via `Relation.Binary`.

{-# OPTIONS --cubical-compatible --safe #-}

open import Relation.Binary.Core

module Relation.Binary.Structures
  {a ℓ} {A : Set a} -- The underlying set
  (_≈_ : Rel A ℓ)   -- The underlying equality relation
  where

open import Data.Product.Base using (proj₁; proj₂; _,_)
open import Level using (Level; _⊔_)
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Consequences
  using (tri⇒dec≈; tri⇒dec<; trans∧irr⇒asym)
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
  reflexive ≡.refl = refl

  isPartialEquivalence : IsPartialEquivalence
  isPartialEquivalence = record
    { sym = sym
    ; trans = trans
    }


record IsDecEquivalence : Set (a ⊔ ℓ) where
  infix 4 _≈?_ _≟_
  field
    isEquivalence : IsEquivalence
    _≈?_          : Decidable _≈_

  open IsEquivalence isEquivalence public

  _≟_ = _≈?_
  {-# WARNING_ON_USAGE _≟_
  "Warning: _≟_ was deprecated in v2.4.
  Please use _≈?_ instead. "
  #-}


------------------------------------------------------------------------
-- Preorders
------------------------------------------------------------------------

record IsPreorder (_≲_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence
    -- Reflexivity is expressed in terms of the underlying equality:
    reflexive     : _≈_ ⇒ _≲_
    trans         : Transitive _≲_

  module Eq = IsEquivalence isEquivalence

  refl : Reflexive _≲_
  refl = reflexive Eq.refl

  ≲-respˡ-≈ : _≲_ Respectsˡ _≈_
  ≲-respˡ-≈ x≈y x∼z = trans (reflexive (Eq.sym x≈y)) x∼z

  ≲-respʳ-≈ : _≲_ Respectsʳ _≈_
  ≲-respʳ-≈ x≈y z∼x = trans z∼x (reflexive x≈y)

  ≲-resp-≈ : _≲_ Respects₂ _≈_
  ≲-resp-≈ = ≲-respʳ-≈ , ≲-respˡ-≈

  ∼-respˡ-≈ = ≲-respˡ-≈
  {-# WARNING_ON_USAGE ∼-respˡ-≈
  "Warning: ∼-respˡ-≈ was deprecated in v2.0.
  Please use ≲-respˡ-≈ instead. "
  #-}
  ∼-respʳ-≈ = ≲-respʳ-≈
  {-# WARNING_ON_USAGE ∼-respʳ-≈
  "Warning: ∼-respʳ-≈ was deprecated in v2.0.
  Please use ≲-respʳ-≈ instead. "
  #-}
  ∼-resp-≈ = ≲-resp-≈
  {-# WARNING_ON_USAGE ∼-resp-≈
  "Warning: ∼-resp-≈ was deprecated in v2.0.
  Please use ≲-resp-≈ instead. "
  #-}


record IsTotalPreorder (_≲_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≲_
    total      : Total _≲_

  open IsPreorder isPreorder public


record IsDecPreorder (_≲_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≲_
    _≈?_       : Decidable _≈_
    _≲?_       : Decidable _≲_

  open IsPreorder isPreorder public
    hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence
    isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≈?_          = _≈?_
      }

    open IsDecEquivalence isDecEquivalence public


------------------------------------------------------------------------
-- Partial orders
------------------------------------------------------------------------

record IsPartialOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≤_
    antisym    : Antisymmetric _≈_ _≤_

  open IsPreorder isPreorder public
    renaming
    ( ≲-respˡ-≈ to ≤-respˡ-≈
    ; ≲-respʳ-≈ to ≤-respʳ-≈
    ; ≲-resp-≈  to ≤-resp-≈
    )


record IsDecPartialOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  infix 4 _≈?_ _≤?_
  field
    isPartialOrder : IsPartialOrder _≤_
    _≈?_           : Decidable _≈_
    _≤?_           : Decidable _≤_

  open IsPartialOrder isPartialOrder public
    hiding (module Eq)

  isDecPreorder : IsDecPreorder _≤_
  isDecPreorder = record
    { isPreorder = isPreorder
    ; _≈?_ = _≈?_
    ; _≲?_ = _≤?_
    }

  open IsDecPreorder isDecPreorder public
    using (module Eq)

  open Eq public using (_≟_)


record IsStrictPartialOrder (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence
    irrefl        : Irreflexive _≈_ _<_
    trans         : Transitive _<_
    <-resp-≈      : _<_ Respects₂ _≈_

  module Eq = IsEquivalence isEquivalence

  asym : Asymmetric _<_
  asym {x} {y} = trans∧irr⇒asym Eq.refl trans irrefl {x = x} {y}

  <-respʳ-≈ : _<_ Respectsʳ _≈_
  <-respʳ-≈ = proj₁ <-resp-≈

  <-respˡ-≈ : _<_ Respectsˡ _≈_
  <-respˡ-≈ = proj₂ <-resp-≈


record IsDecStrictPartialOrder (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  infix 4 _≈?_ _<?_
  field
    isStrictPartialOrder : IsStrictPartialOrder _<_
    _≈?_                 : Decidable _≈_
    _<?_                 : Decidable _<_

  private
    module SPO = IsStrictPartialOrder isStrictPartialOrder

  open SPO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence
    isDecEquivalence = record
      { isEquivalence = SPO.isEquivalence
      ; _≈?_          = _≈?_
      }

    open IsDecEquivalence isDecEquivalence public

  open Eq public using (_≟_)


------------------------------------------------------------------------
-- Total orders
------------------------------------------------------------------------

record IsTotalOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≤_
    total          : Total _≤_

  open IsPartialOrder isPartialOrder public

  isTotalPreorder : IsTotalPreorder _≤_
  isTotalPreorder = record
    { isPreorder = isPreorder
    ; total      = total
    }


record IsDecTotalOrder (_≤_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  infix 4 _≈?_ _≤?_
  field
    isTotalOrder : IsTotalOrder _≤_
    _≈?_         : Decidable _≈_
    _≤?_         : Decidable _≤_

  open IsTotalOrder isTotalOrder public
    hiding (module Eq)

  isDecPartialOrder : IsDecPartialOrder _≤_
  isDecPartialOrder = record
    { isPartialOrder = isPartialOrder
    ; _≈?_           = _≈?_
    ; _≤?_           = _≤?_
    }

  open IsDecPartialOrder isDecPartialOrder public
    using (isDecPreorder; module Eq)

  open Eq public using (_≟_)


-- Note that these orders are decidable. The current implementation
-- of `Trichotomous` subsumes irreflexivity and asymmetry. See
-- `Relation.Binary.Structures.Biased` for ways of constructing this
-- record without having to prove `isStrictPartialOrder`.

record IsStrictTotalOrder (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isStrictPartialOrder : IsStrictPartialOrder _<_
    compare              : Trichotomous _≈_ _<_

  open IsStrictPartialOrder isStrictPartialOrder public
    hiding (module Eq)

  -- `Trichotomous` necessarily separates out the equality case so
  --  it implies decidability.
  infix 4 _≈?_ _<?_

  _≈?_ : Decidable _≈_
  _≈?_ = tri⇒dec≈ compare

  _<?_ : Decidable _<_
  _<?_ = tri⇒dec< compare

  isDecStrictPartialOrder : IsDecStrictPartialOrder _<_
  isDecStrictPartialOrder = record
    { isStrictPartialOrder = isStrictPartialOrder
    ; _≈?_                  = _≈?_
    ; _<?_                 = _<?_
    }

  -- Redefine the `Eq` module to include decidability proofs
  module Eq where

    isDecEquivalence : IsDecEquivalence
    isDecEquivalence = record
      { isEquivalence = isEquivalence
      ; _≈?_          = _≈?_
      }

    open IsDecEquivalence isDecEquivalence public

  open Eq public using (_≟_)

  isDecEquivalence : IsDecEquivalence
  isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≈?_          = _≈?_
    }
  {-# WARNING_ON_USAGE isDecEquivalence
  "Warning: isDecEquivalence was deprecated in v2.0.
  Please use Eq.isDecEquivalence instead. "
  #-}

record IsDenseLinearOrder (_<_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    isStrictTotalOrder : IsStrictTotalOrder _<_
    dense              : Dense _<_

  open IsStrictTotalOrder isStrictTotalOrder public


------------------------------------------------------------------------
-- Apartness relations
------------------------------------------------------------------------

record IsApartnessRelation (_#_ : Rel A ℓ₂) : Set (a ⊔ ℓ ⊔ ℓ₂) where
  field
    irrefl  : Irreflexive _≈_ _#_
    sym     : Symmetric _#_
    cotrans : Cotransitive _#_

  _¬#_ : A → A → Set _
  x ¬# y = ¬ (x # y)
