------------------------------------------------------------------------
-- The Agda standard library
--
-- An explanation about how mathematical hierarchies are laid out.
------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

module README.Design.Hierarchies where

open import Data.Sum using (_⊎_)
open import Level using (Level; _⊔_; suc)
open import Relation.Binary using (_Preserves₂_⟶_⟶_)

private
  variable
    a b ℓ : Level
    A : Set a

------------------------------------------------------------------------
-- Introduction
------------------------------------------------------------------------

-- One of the key design decisions facing the library is how to handle
-- mathematical hierarchies, e.g.
--   ∙ Binary relations: preorder → partial order → total order
--                                ↘ equivalence
--   ∙ Algebraic structures: magma → semigroup → monoid → group
--                                 ↘ band → semilattice
--
-- Some of the hierarchies in the library are:
--   ∙ Algebra
--   ∙ Function
--   ∙ Relation.Binary
--   ∙ Relation.Binary.Indexed
--
-- A given hierarchy `X` is always split into 4 seperate folders:
--   ∙ X.Core
--   ∙ X.Definitions
--   ∙ X.Structures
--   ∙ X.Bundles
-- all four of which are publicly re-exported by `X` itself.
--
-- Additionally a hierarchy `X` may contain additional files
--   ∙ X.Consequences
--   ∙ X.Constructs
--   ∙ X.Properties
--   ∙ X.Morphisms
--
-- Descriptions of these modules are now described below using the
-- running example of the `Relation.Binary` and `Algebra` hierarchies.

-- Note that we redefine everything here for illustrative purposes,
-- and that the definitions given below may be slightly simpler
-- than the real definitions in order to focus on the points being
-- discussed.


------------------------------------------------------------------------
-- Main hierarchy modules
------------------------------------------------------------------------

------------------------------------------------------------------------
-- X.Core

-- The Core module contains the basic units of the hierarchy.

-- For example for binary relations these are homoegeneous and
-- heterogeneous binary relations:

REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = A → A → Set ℓ

-- and in Algebra these are unary and binary operators, e.g.

Op₁ : Set a → Set a
Op₁ A = A → A

Op₂ : Set a → Set a
Op₂ A = A → A → A


------------------------------------------------------------------------
-- X.Definitions

-- The Definitions module defines the various properties that the
-- basic units of the hierarchy may have.

-- For example in Relation.Binary this includes reflexivity,
-- transitivity etc.

Reflexive : Rel A ℓ → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x

Symmetric : Rel A ℓ → Set _
Symmetric _∼_ = ∀ {x y} → x ∼ y → y ∼ x

Transitive : Rel A ℓ → Set _
Transitive _∼_ = ∀ {x y z} → x ∼ y → y ∼ z → x ∼ z

Total : Rel A ℓ → Set _
Total _∼_ = ∀ x y → x ∼ y ⊎ y ∼ x

-- For example in Algebra these are associativity, commutativity.
-- Note that all definitions for Algebra are based on some notion of
-- underlying equality.

Associative : Rel A ℓ → Op₂ A → Set _
Associative _≈_ _∙_ = ∀ x y z → ((x ∙ y) ∙ z) ≈ (x ∙ (y ∙ z))

Commutative : Rel A ℓ → Op₂ A → Set _
Commutative _≈_ _∙_ = ∀ x y → (x ∙ y) ≈ (y ∙ x)

LeftIdentity : Rel A ℓ → A → Op₂ A → Set _
LeftIdentity _≈_ e _∙_ = ∀ x → (e ∙ x) ≈ x

RightIdentity : Rel A ℓ → A → Op₂ A → Set _
RightIdentity _≈_ e _∙_ = ∀ x → (x ∙ e) ≈ x

-- Note that the types in `Definitions` modules are not meant to express
-- the full concept on their own. For example the `Associative` type does
-- not require the underlying relation to be an equivalence relation.
-- Instead they are designed to aid the modular reuse of the core
-- concepts. The complete concepts are captured in various
-- structures/bundles where the definitions are correctly used in
-- context.


------------------------------------------------------------------------
-- X.Structures

-- When an abstract hierarchy of some sort (for instance semigroup →
-- monoid → group) is included in the library the basic approach is to
-- specify the properties of every concept in terms of a record
-- containing just properties, parameterised on the underlying
-- sets, relations and operations. For example:

record IsEquivalence {A : Set a}
                     (_≈_ : Rel A ℓ)
                     : Set (a ⊔ ℓ)
                     where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

-- More specific concepts are then specified in terms of the simpler
-- ones:

record IsMagma {A : Set a} (≈ : Rel A ℓ) (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence ≈
    ∙-cong        : ∙ Preserves₂ ≈ ⟶ ≈ ⟶ ≈

record IsSemigroup {A : Set a} (≈ : Rel A ℓ) (∙ : Op₂ A) : Set (a ⊔ ℓ) where
  field
    isMagma      : IsMagma ≈ ∙
    associative  : Associative ≈ ∙

  open IsMagma isMagma public

-- Note here that `open IsMagma isMagma public` ensures that the
-- fields of the `isMagma` record can be accessed directly; this
-- technique enables the user of an `IsSemigroup` record to use underlying
-- records without having to manually open an entire record hierarchy.
-- This is not always possible, though. Consider the following definition
-- of preorders:

record IsPreorder {A : Set a}
                  (_≈_ : Rel A ℓ) -- The underlying equality.
                  (_∼_ : Rel A ℓ) -- The relation.
                  : Set (a ⊔ ℓ) where
  field
    isEquivalence : IsEquivalence _≈_
    refl          : Reflexive _∼_
    trans         : Transitive _∼_

  module Eq = IsEquivalence isEquivalence

-- The IsEquivalence field in IsPreorder is not opened publicly because
-- the `refl` and `trans` fields would clash with those in the
-- `IsPreorder` record. Instead we provide an internal module and the
-- equality fields can be accessed via `Eq.refl` and `Eq.trans`.


------------------------------------------------------------------------
-- X.Bundles

-- Although structures are useful for describing the properties of a
-- given set of operations/relations, sometimes you don't require the
-- properties to hold for a given set of objects but only that such a
-- set of objects exists. In this case bundles are what you're after.

-- Each structure has a corresponding bundle that include the structure
-- along with the corresponding sets, relations and operations as
-- fields.

record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

-- The contents of the structure is always re-exported publicly,
-- providing access to its fields.

record Magma c ℓ : Set (suc (c ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    isMagma : IsMagma _≈_ _∙_

  open IsMagma isMagma public


record Semigroup : Set (suc (a ⊔ ℓ)) where
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier     : Set a
    _≈_         : Rel Carrier ℓ
    _∙_         : Op₂ Carrier
    isSemigroup : IsSemigroup _≈_ _∙_

  open IsSemigroup isSemigroup public

  magma : Magma a ℓ
  magma = record { isMagma = isMagma }

-- Note that the Semigroup record does not include a Magma field.
-- Instead the Semigroup record includes a "repackaging function"
-- semigroup which converts a Magma to a Semigroup.

-- The above setup may seem a bit complicated, but it has been arrived
-- at after a lot of thought and is designed to both make the hierarchies
-- easy to work with whilst also providing enough flexibility for the
-- different applications of their concepts.

-- NOTE: bundles for the function hierarchy are designed a little
-- differently, as a function with an unknown domain an codomain is
-- of little use.

------------------------------------------------------------------------
-- Other hierarchy modules
------------------------------------------------------------------------

------------------------------------------------------------------------
-- X.Consequences

-- The "consequences" modules contains proofs for how the different
-- types in the `Definitions` module relate to each other. For example:
-- that any total relation is reflexive or that commutativity allows
-- one to translate between left and right identities.

total⇒refl : ∀ {_∼_ : Rel A ℓ} → Total _∼_ → Reflexive _∼_
total⇒refl = {!!}

idˡ+comm⇒idʳ : ∀ {_≈_ : Rel A ℓ} {e _∙_} → Commutative _≈_ _∙_ →
               LeftIdentity _≈_ e _∙_ →  RightIdentity _≈_ e _∙_
idˡ+comm⇒idʳ = {!!}

------------------------------------------------------------------------
-- X.Construct

-- The "construct" folder contains various generic ways of constructing
-- new instances of the hierarchy. For example

import Relation.Binary.Construct.Intersection

-- takes in two relations and forms the new relation that says two
-- elements are only related if they are related via both of the
-- original relations.

-- These files are layed out in four parts, mimicking the main modules
-- of the hierarchy itself. First they define the new relation, then
-- subsequently how the definitions, then structures and finally
-- bundles can be translated across to it.

------------------------------------------------------------------------
-- X.Morphisms

-- The `Morphisms` folder is a sub-hierarchy containing relationships
-- such homomorphisms, monomorphisms and isomorphisms between the
-- structures and bundles in the hierarchy.

------------------------------------------------------------------------
-- X.Properties

-- The `Properties` folder contains additional proofs about the theory
-- of each bundle. They are usually designed so as a bundle's
-- `Properties` file re-exports the contents of the `Properties` files
-- above it in the hierarchy. For example
-- `Algebra.Properties.AbelianGroup` re-exports the contents of
-- `Algebra.Properties.Group`.
