------------------------------------------------------------------------
-- The Agda standard library
--
-- Definitions of 'raw' bundles for module-like algebraic structures
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Algebra.Module.Bundles.Raw where

open import Algebra.Bundles.Raw
open import Algebra.Core
open import Algebra.Module.Core
open import Level
open import Relation.Nullary.Negation.Core using (¬_)
open import Relation.Binary.Core using (Rel)

private
  variable
    r ℓr s ℓs : Level

------------------------------------------------------------------------
-- Raw left modules
------------------------------------------------------------------------

record RawLeftSemimodule (R : Set r) m ℓm : Set (r ⊔ suc (m ⊔ ℓm)) where
  infixr 7 _*ₗ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ R Carrierᴹ
    0ᴹ : Carrierᴹ

  +ᴹ-rawMonoid : RawMonoid m ℓm
  +ᴹ-rawMonoid = record
    { _≈_ = _≈ᴹ_
    ; _∙_ = _+ᴹ_
    ; ε = 0ᴹ
    }

  open RawMonoid +ᴹ-rawMonoid public
    using ()
    renaming (rawMagma to +ᴹ-rawMagma; _≉_ to _≉ᴹ_)

record RawLeftModule (R : Set r) m ℓm : Set (r ⊔ suc (m ⊔ ℓm)) where
  infix 8 -ᴹ_
  infixr 7 _*ₗ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ R Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ

  rawLeftSemimodule : RawLeftSemimodule R m ℓm
  rawLeftSemimodule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ₗ_ = _*ₗ_
    ; 0ᴹ = 0ᴹ
    }

  open RawLeftSemimodule rawLeftSemimodule public
    using (+ᴹ-rawMagma; +ᴹ-rawMonoid; _≉ᴹ_)

  +ᴹ-rawGroup : RawGroup m ℓm
  +ᴹ-rawGroup = record
    { _≈_ = _≈ᴹ_
    ; _∙_ = _+ᴹ_
    ; ε = 0ᴹ
    ; _⁻¹ = -ᴹ_
    }

------------------------------------------------------------------------
-- Raw right modules
------------------------------------------------------------------------

record RawRightSemimodule (R : Set r) m ℓm : Set (r ⊔ suc (m ⊔ ℓm)) where
  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᵣ_ : Opᵣ R Carrierᴹ
    0ᴹ : Carrierᴹ

  +ᴹ-rawMonoid : RawMonoid m ℓm
  +ᴹ-rawMonoid = record
    { _≈_ = _≈ᴹ_
    ; _∙_ = _+ᴹ_
    ; ε = 0ᴹ
    }

  open RawMonoid +ᴹ-rawMonoid public
    using ()
    renaming (rawMagma to +ᴹ-rawMagma; _≉_ to _≉ᴹ_)

record RawRightModule (R : Set r) m ℓm : Set (r ⊔ suc (m ⊔ ℓm)) where
  infix 8 -ᴹ_
  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ᵣ_ : Opᵣ R Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ

  rawRightSemimodule : RawRightSemimodule R m ℓm
  rawRightSemimodule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ᵣ_ = _*ᵣ_
    ; 0ᴹ = 0ᴹ
    }

  open RawRightSemimodule rawRightSemimodule public
    using (+ᴹ-rawMagma; +ᴹ-rawMonoid; _≉ᴹ_)

  +ᴹ-rawGroup : RawGroup m ℓm
  +ᴹ-rawGroup = record
    { _≈_ = _≈ᴹ_
    ; _∙_ = _+ᴹ_
    ; ε = 0ᴹ
    ; _⁻¹ = -ᴹ_
    }

------------------------------------------------------------------------
-- Bimodules
------------------------------------------------------------------------

record RawBisemimodule (R : Set r) (S : Set s) m ℓm : Set (r ⊔ s ⊔ suc (m ⊔ ℓm)) where
  infixr 7 _*ₗ_
  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ R Carrierᴹ
    _*ᵣ_ : Opᵣ S Carrierᴹ
    0ᴹ : Carrierᴹ

  rawLeftSemimodule : RawLeftSemimodule R m ℓm
  rawLeftSemimodule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ₗ_ = _*ₗ_
    ; 0ᴹ = 0ᴹ
    }

  rawRightSemimodule : RawRightSemimodule S m ℓm
  rawRightSemimodule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ᵣ_ = _*ᵣ_
    ; 0ᴹ = 0ᴹ
    }

  open RawLeftSemimodule rawLeftSemimodule public
    using (+ᴹ-rawMagma; +ᴹ-rawMonoid; _≉ᴹ_)

record RawBimodule (R : Set r) (S : Set s) m ℓm : Set (r ⊔ s ⊔ suc (m ⊔ ℓm)) where
  infix 8 -ᴹ_
  infixr 7 _*ₗ_
  infixl 7 _*ᵣ_
  infixl 6 _+ᴹ_
  infix 4 _≈ᴹ_

  field
    Carrierᴹ : Set m
    _≈ᴹ_ : Rel Carrierᴹ ℓm
    _+ᴹ_ : Op₂ Carrierᴹ
    _*ₗ_ : Opₗ R Carrierᴹ
    _*ᵣ_ : Opᵣ S Carrierᴹ
    0ᴹ : Carrierᴹ
    -ᴹ_ : Op₁ Carrierᴹ

  rawLeftModule : RawLeftModule R m ℓm
  rawLeftModule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ₗ_ = _*ₗ_
    ; 0ᴹ = 0ᴹ
    ; -ᴹ_ = -ᴹ_
    }

  rawRightModule : RawRightModule S m ℓm
  rawRightModule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ᵣ_ = _*ᵣ_
    ; 0ᴹ = 0ᴹ
    ; -ᴹ_ = -ᴹ_
    }

  rawBisemimodule : RawBisemimodule R S m ℓm
  rawBisemimodule = record
    { _≈ᴹ_ = _≈ᴹ_
    ; _+ᴹ_ = _+ᴹ_
    ; _*ₗ_ = _*ₗ_
    ; _*ᵣ_ = _*ᵣ_
    ; 0ᴹ = 0ᴹ
    }

  open RawBisemimodule rawBisemimodule public
    using (+ᴹ-rawMagma; +ᴹ-rawMonoid; rawLeftSemimodule; rawRightSemimodule; _≉ᴹ_)

  open RawLeftModule rawLeftModule public
    using (+ᴹ-rawGroup)

------------------------------------------------------------------------
-- Modules over commutative structures
------------------------------------------------------------------------

RawSemimodule : ∀ (R : Set r) m ℓm → Set (r ⊔ suc (m ⊔ ℓm))
RawSemimodule R = RawBisemimodule R R

module RawSemimodule {R : Set r} {m ℓm} (M : RawSemimodule R m ℓm) where
  open RawBisemimodule M public

  rawBisemimodule : RawBisemimodule R R m ℓm
  rawBisemimodule = M

RawModule : ∀ (R : Set r) m ℓm → Set (r ⊔ suc(m ⊔ ℓm))
RawModule R = RawBimodule R R

module RawModule {R : Set r} {m ℓm} (M : RawModule R m ℓm) where
  open RawBimodule M public

  rawBimodule : RawBimodule R R m ℓm
  rawBimodule = M

  rawSemimodule : RawSemimodule R m ℓm
  rawSemimodule = rawBisemimodule
