------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary or Relation.Binary.PropositionalEquality.

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Core where

open import Agda.Builtin.Equality using (_≡_) renaming (refl to ≡-refl)

open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Data.Sum.Base using (_⊎_)
open import Function using (_on_; flip)
open import Level
open import Relation.Nullary using (Dec; ¬_)

------------------------------------------------------------------------
-- Binary relations

-- Heterogeneous binary relations

REL : ∀ {a b} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ suc ℓ)
REL A B ℓ = A → B → Set ℓ

-- Homogeneous binary relations

Rel : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Rel A ℓ = REL A A ℓ

------------------------------------------------------------------------
-- Simple properties of binary relations

infixr 4 _⇒_ _=[_]⇒_

-- Implication/containment. Could also be written ⊆.

_⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL A B ℓ₂ → Set _
P ⇒ Q = ∀ {i j} → P i j → Q i j

-- Generalised implication. If P ≡ Q it can be read as "f preserves P".

_=[_]⇒_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
          Rel A ℓ₁ → (A → B) → Rel B ℓ₂ → Set _
P =[ f ]⇒ Q = P ⇒ (Q on f)

-- A synonym, along with a binary variant.

_Preserves_⟶_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
                (A → B) → Rel A ℓ₁ → Rel B ℓ₂ → Set _
f Preserves P ⟶ Q = P =[ f ]⇒ Q

_Preserves₂_⟶_⟶_ :
  ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
  (A → B → C) → Rel A ℓ₁ → Rel B ℓ₂ → Rel C ℓ₃ → Set _
_+_ Preserves₂ P ⟶ Q ⟶ R =
  ∀ {x y u v} → P x y → Q u v → R (x + u) (y + v)

-- Reflexivity of _∼_ can be expressed as _≈_ ⇒ _∼_, for some
-- underlying equality _≈_. However, the following variant is often
-- easier to use.

Reflexive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Reflexive _∼_ = ∀ {x} → x ∼ x

-- Irreflexivity is defined using an underlying equality.

Irreflexive : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
              REL A B ℓ₁ → REL A B ℓ₂ → Set _
Irreflexive _≈_ _<_ = ∀ {x y} → x ≈ y → ¬ (x < y)

-- Generalised symmetry.

Sym : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
      REL A B ℓ₁ → REL B A ℓ₂ → Set _
Sym P Q = P ⇒ flip Q

Symmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Symmetric _∼_ = Sym _∼_ _∼_

-- Generalised transitivity.

Trans : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
        REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
Trans P Q R = ∀ {i j k} → P i j → Q j k → R i k

-- A variant of Trans.

TransFlip : ∀ {a b c ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} {C : Set c} →
            REL A B ℓ₁ → REL B C ℓ₂ → REL A C ℓ₃ → Set _
TransFlip P Q R = ∀ {i j k} → Q j k → P i j → R i k

Transitive : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Transitive _∼_ = Trans _∼_ _∼_ _∼_

-- Generalised antisymmetry

Antisym : ∀ {a b ℓ₁ ℓ₂ ℓ₃} {A : Set a} {B : Set b} →
          REL A B ℓ₁ → REL B A ℓ₂ → REL A B ℓ₃ → Set _
Antisym R S E = ∀ {i j} → R i j → S j i → E i j

Antisymmetric : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric _≈_ _≤_ = Antisym _≤_ _≤_ _≈_

Asymmetric : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Asymmetric _<_ = ∀ {x y} → x < y → ¬ (y < x)

-- Generalised connex.

Conn : ∀ {a b p q} {A : Set a} {B : Set b} → REL A B p → REL B A q → Set _
Conn P Q = ∀ x y → P x y ⊎ Q y x

Total : ∀ {a ℓ} {A : Set a} → Rel A ℓ → Set _
Total _∼_ = Conn _∼_ _∼_

data Tri {a b c} (A : Set a) (B : Set b) (C : Set c) :
         Set (a ⊔ b ⊔ c) where
  tri< : ( a :   A) (¬b : ¬ B) (¬c : ¬ C) → Tri A B C
  tri≈ : (¬a : ¬ A) ( b :   B) (¬c : ¬ C) → Tri A B C
  tri> : (¬a : ¬ A) (¬b : ¬ B) ( c :   C) → Tri A B C

Trichotomous : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Trichotomous _≈_ _<_ = ∀ x y → Tri (x < y) (x ≈ y) (x > y)
  where _>_ = flip _<_

Maximum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set _
Maximum _≤_ ⊤ = ∀ x → x ≤ ⊤

Minimum : ∀ {a ℓ} {A : Set a} → Rel A ℓ → A → Set _
Minimum _≤_ = Maximum (flip _≤_)

_Respects_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → (A → Set ℓ₁) → Rel A ℓ₂ → Set _
P Respects _∼_ = ∀ {x y} → x ∼ y → P x → P y

_Respectsʳ_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
P Respectsʳ _∼_ = ∀ {x} → (P x) Respects _∼_

_Respectsˡ_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
P Respectsˡ _∼_ = ∀ {y} → (flip P y) Respects _∼_

_Respects₂_ : ∀ {a ℓ₁ ℓ₂} {A : Set a} → Rel A ℓ₁ → Rel A ℓ₂ → Set _
P Respects₂ _∼_ = (P Respectsʳ _∼_) × (P Respectsˡ _∼_)

Substitutive : ∀ {a ℓ₁} {A : Set a} → Rel A ℓ₁ → (ℓ₂ : Level) → Set _
Substitutive {A = A} _∼_ p = (P : A → Set p) → P Respects _∼_

Decidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

WeaklyDecidable : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
WeaklyDecidable _∼_ = ∀ x y → Maybe (x ∼ y)

Irrelevant : ∀ {a b ℓ} {A : Set a} {B : Set b} → REL A B ℓ → Set _
Irrelevant _∼_ = ∀ {x y} (a : x ∼ y) (b : x ∼ y) → a ≡ b

record NonEmpty {a b ℓ} {A : Set a} {B : Set b}
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

record IsEquivalence {a ℓ} {A : Set a}
                     (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  field
    refl  : Reflexive _≈_
    sym   : Symmetric _≈_
    trans : Transitive _≈_

  reflexive : _≡_ ⇒ _≈_
  reflexive ≡-refl = refl
