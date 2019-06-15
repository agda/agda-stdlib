------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of binary relations
------------------------------------------------------------------------

-- Note that all the definitions in this file are re-exported by
-- `Relation.Binary`.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Core where

open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡-refl)

open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function using (_on_; flip)
open import Level
open import Relation.Nullary using (Dec; ¬_)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ ℓ₃ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definition.
------------------------------------------------------------------------

-- Heterogeneous binary relations

REL : Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ

------------------------------------------------------------------------
-- Simple properties
------------------------------------------------------------------------

infixr 4 _⇒_ _=[_]⇒_

-- Implication/containment - could also be written _⊆_.

_⇒_ : REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇒ Q = ∀ {i j} → P i j → Q i j

-- Generalised implication - if P ≡ Q it can be read as "f preserves P".

_=[_]⇒_ : Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)

-- A synonym for _=[_]⇒_.

_Preserves_⟶_ : (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

-- A binary variant of _Preserves_⟶_.

_Preserves₂_⟶_⟶_ : (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_+_ Preserves₂ P ⟶ Q ⟶ R =
  ∀ {x y u v} → P x y → Q u v → R (x + u) (y + v)

-- Reflexivity - defined without an underlying equality. It could
-- alternatively be defined as `_≈_ ⇒ _∼_` for some equality `_≈_`.

-- Confusingly the convention in the library is to use the name "refl"
-- for proofs of Reflexive and `reflexive` for proofs of type `_≈_ ⇒ _∼_`,
-- e.g. in the definition of `IsEquivalence` later in this file. This
-- convention is a legacy from the early days of the library.

Reflexive : Rel A ℓ → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x

-- Generalised symmetry.

Sym : REL A B ℓ₁ → REL B A ℓ₂ → Set _
Sym P Q = P ⇒ flip Q

-- Symmetry.

Symmetric : Rel A ℓ → Set _
Symmetric _∼_ = Sym _∼_ _∼_

-- Generalised transitivity.

Trans : REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

-- A flipped variant of generalised transitivity.

TransFlip : REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k

-- Transitivity.

Transitive : Rel A ℓ → Set _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

-- Generalised antisymmetry

Antisym : REL A B ℓ₁ → REL B A ℓ₂ → REL A B ℓ₃ → Set _
Antisym R S E = ∀ {i j} → R i j → S j i → E i j

-- Antisymmetry.

Antisymmetric : Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric _≈_ _≤_ = Antisym _≤_ _≤_ _≈_

-- Irreflexivity - this is defined terms of the underlying equality.

Irreflexive : REL A B ℓ₁ → REL A B ℓ₂ → Set _
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)

-- Asymmetry.

Asymmetric : Rel A ℓ → Set _
Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)

-- Generalised connex - exactly one of the two relations holds.

Connex : REL A B ℓ₁ → REL B A ℓ₂ → Set _
Connex P Q = ∀ x y → P x y ⊎ Q y x

-- Totality.

Total : Rel A ℓ → Set _
Total _∼_ = Connex _∼_ _∼_

-- Generalised trichotomy - exactly one of three types has a witness.

data Tri (A : Set a) (B : Set b) (C : Set c) : Set (a ⊔ b ⊔ c) where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

-- Trichotomy.

Trichotomous : Rel A ℓ₁ → Rel A ℓ₂ → Set _
Trichotomous _≈_ _<_ = ∀ x y → Tri (x < y) (x ≈ y) (x > y)
  where _>_ = flip _<_

-- Generalised maximum element.

Max : REL A B ℓ → B → Set _
Max _≤_ T = ∀ x → x ≤ T

-- Maximum element.

Maximum : Rel A ℓ → A → Set _
Maximum = Max

-- Generalised minimum element.

Min : REL A B ℓ → A → Set _
Min R = Max (flip R)

-- Minimum element.

Minimum : Rel A ℓ → A → Set _
Minimum = Min

-- Unary relations respecting a binary relation.

_⟶_Respects_ : (A → Set ℓ₁) → (B → Set ℓ₂) → REL A B ℓ₃ → Set _
P ⟶ Q Respects _∼_ = ∀ {x y} → x ∼ y → P x → Q y

-- Unary relation respects a binary relation.

_Respects_ : (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = P ⟶ P Respects _∼_

-- Right respecting - relatedness is preserved on the right by equality.

_Respectsʳ_ : REL A B ℓ₁ → Rel B ℓ₂ → Set _
_∼_ Respectsʳ _≈_ = ∀ {x} → (x ∼_) Respects _≈_

-- Left respecting - relatedness is preserved on the left by equality.

_Respectsˡ_ : REL A B ℓ₁ → Rel A ℓ₂ → Set _
P Respectsˡ _∼_ = ∀ {y} → (flip P y) Respects _∼_

-- Respecting - relatedness is preserved on both sides by equality

_Respects₂_ : Rel A ℓ₁ → Rel A ℓ₂ → Set _
P Respects₂ _∼_ = (P Respectsʳ _∼_) × (P Respectsˡ _∼_)

-- Substitutivity - any two related elements satisfy exactly the same
-- set of unary relations. Note that only the various derivatives
-- of propositional equality can satisfy this property.

Substitutive : Rel A ℓ₁ → (ℓ₂ : Level) → Set _
Substitutive {A = A} _∼_ p = (P : A → Set p) → P Respects _∼_

-- Decidability - it is possible to determine whether a given pair of
-- elements are related.

Decidable : REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

DecidableEquality : (A : Set a) → Set _
DecidableEquality A = Decidable {A = A} _≡_

-- Weak decidability - it is sometimes possible to determine if a given
-- pair of elements are related.

WeaklyDecidable : REL A B ℓ → Set _
WeaklyDecidable _∼_ = ∀ x y → Maybe (x ∼ y)

-- Irrelevancy - all proofs that a given pair of elements are related
-- are indistinguishable.

Irrelevant : REL A B ℓ → Set _
Irrelevant _∼_ = ∀ {x y} (a b : x ∼ y) → a ≡ b

-- Recomputability - we can rebuild a relevant proof given an
-- irrelevant one.

Recomputable : REL A B ℓ → Set _
Recomputable _∼_ = ∀ {x y} → .(x ∼ y) → x ∼ y

-- Universal - all pairs of elements are related

Universal : REL A B ℓ → Set _
Universal _∼_ = ∀ x y → x ∼ y

-- Non-emptiness - at least one pair of elements are related.

record NonEmpty {A : Set a} {B : Set b}
                (T : REL A B ℓ) : Set (a ⊔ b ⊔ ℓ) where
  constructor nonEmpty
  field
    {x}   : A
    {y}   : B
    proof : T x y

------------------------------------------------------------------------
-- Equivalence relations

-- The preorders of this library are defined in terms of an underlying
-- equivalence relation, and hence equivalence relations are not
-- defined in terms of preorders.

-- This record is defined here instead of with the rest of the
-- structures in `Relation.Binary` due to dependency cyles with
-- `Relation.Binary.PropositionalEquality`.

record IsEquivalence {A : Set a} (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  reflexive : _≡_ ⇒ _≈_
  reflexive ≡-refl = refl



------------------------------------------------------------------------
-- DEPRECATED NAMES
------------------------------------------------------------------------
-- Please use the new names as continuing support for the old names is
-- not guaranteed.

-- Version 1.1

Conn = Connex
{-# WARNING_ON_USAGE Conn
"Warning: Conn was deprecated in v1.1.
Please use Connex instead."
#-}
