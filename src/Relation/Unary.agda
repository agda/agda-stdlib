------------------------------------------------------------------------
-- The Agda standard library
--
-- Unary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Relation.Unary where

open import Data.Empty
open import Data.Unit.Base using (⊤)
open import Data.Product
open import Data.Sum using (_⊎_; [_,_])
open import Function
open import Level
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

------------------------------------------------------------------------
-- Unary relations

Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Pred A ℓ = A → Set ℓ

------------------------------------------------------------------------
-- Unary relations can be seen as sets
-- i.e. they can be seen as subsets of the universe of discourse.

module _ {a} {A : Set a} where

  ----------------------------------------------------------------------
  -- Special sets

  -- The empty set

  ∅ : Pred A zero
  ∅ = λ _ → ⊥

  -- The singleton set

  ｛_｝ : A → Pred A a
  ｛ x ｝ = x ≡_

  -- The universe

  U : Pred A zero
  U = λ _ → ⊤

  ----------------------------------------------------------------------
  -- Membership

  infix 4 _∈_ _∉_

  _∈_ : ∀ {ℓ} → A → Pred A ℓ → Set _
  x ∈ P = P x

  _∉_ : ∀ {ℓ} → A → Pred A ℓ → Set _
  x ∉ P = ¬ x ∈ P

  ----------------------------------------------------------------------
  -- Subsets

  infix 4 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_

  _⊆_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

  _⊇_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊇ Q = Q ⊆ P

  _⊈_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊈ Q = ¬ (P ⊆ Q)

  _⊉_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊉ Q = ¬ (P ⊇ Q)

  _⊂_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊂ Q = P ⊆ Q × Q ⊈ P

  _⊃_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊃ Q = Q ⊂ P

  _⊄_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊄ Q = ¬ (P ⊂ Q)

  _⊅_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊅ Q = ¬ (P ⊃ Q)

  -- Dashed variants of _⊆_ for when 'x' can't be inferred from 'x ∈ P'.

  infix 4 _⊆′_ _⊇′_ _⊈′_ _⊉′_ _⊂′_ _⊃′_ _⊄′_ _⊅′_

  _⊆′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊆′ Q = ∀ x → x ∈ P → x ∈ Q

  _⊇′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  Q ⊇′ P = P ⊆′ Q

  _⊈′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊈′ Q = ¬ (P ⊆′ Q)

  _⊉′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊉′ Q = ¬ (P ⊇′ Q)

  _⊂′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊂′ Q = P ⊆′ Q × Q ⊈′ P

  _⊃′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊃′ Q = Q ⊂′ P

  _⊄′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊄′ Q = ¬ (P ⊂′ Q)

  _⊅′_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ⊅′ Q = ¬ (P ⊃′ Q)

  ----------------------------------------------------------------------
  -- Properties of sets

  -- Emptiness

  Empty : ∀ {ℓ} → Pred A ℓ → Set _
  Empty P = ∀ x → x ∉ P

  -- Satisfiable

  Satisfiable : ∀ {ℓ} → Pred A ℓ → Set _
  Satisfiable P = ∃ λ x → x ∈ P

  -- Universality

  infix 10 Universal IUniversal
  Universal : ∀ {ℓ} → Pred A ℓ → Set _
  Universal P = ∀ x → x ∈ P

  IUniversal : ∀ {ℓ} → Pred A ℓ → Set _
  IUniversal P = ∀ {x} → x ∈ P

  syntax Universal  P = Π[ P ]
  syntax IUniversal P = ∀[ P ]

  -- Decidability

  Decidable : ∀ {ℓ} → Pred A ℓ → Set _
  Decidable P = ∀ x → Dec (P x)

  -- Irrelevance

  Irrelevant : ∀ {ℓ} → Pred A ℓ → Set _
  Irrelevant P = ∀ {x} (a : P x) (b : P x) → a ≡ b

  ----------------------------------------------------------------------
  -- Operations on sets

  -- Set complement.

  ∁ : ∀ {ℓ} → Pred A ℓ → Pred A ℓ
  ∁ P = λ x → x ∉ P

  -- Positive version of non-disjointness, dual to inclusion.

  infix 4 _≬_

  _≬_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Set _
  P ≬ Q = ∃ λ x → x ∈ P × x ∈ Q

  -- Set union.

  infixr 6 _∪_

  _∪_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q

  -- Set intersection.

  infixr 7 _∩_

  _∩_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ∩ Q = λ x → x ∈ P × x ∈ Q

  -- Implication.

  infixr 8 _⇒_

  _⇒_ : ∀ {ℓ₁ ℓ₂} → Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
  P ⇒ Q = λ x → x ∈ P → x ∈ Q

  -- Infinitary union and intersection.

  infix 10 ⋃ ⋂

  ⋃ : ∀ {ℓ i} (I : Set i) → (I → Pred A ℓ) → Pred A _
  ⋃ I P = λ x → Σ[ i ∈ I ] P i x

  syntax ⋃ I (λ i → P) = ⋃[ i ∶ I ] P

  ⋂ : ∀ {ℓ i} (I : Set i) → (I → Pred A ℓ) → Pred A _
  ⋂ I P = λ x → (i : I) → P i x

  syntax ⋂ I (λ i → P) = ⋂[ i ∶ I ] P

-- Update.

infixr 9 _⊢_

_⊢_ : ∀ {a b} {A : Set a} {B : Set b} {ℓ} → (A → B) → Pred B ℓ → Pred A ℓ
f ⊢ P = λ x → P (f x)

------------------------------------------------------------------------
-- Unary relation combinators

infixr  2 _⟨×⟩_
infixr  2 _⟨⊙⟩_
infixr  1 _⟨⊎⟩_
infixr  0 _⟨→⟩_
infixl  9 _⟨·⟩_
infix  10 _~
infixr  9 _⟨∘⟩_
infixr  2 _//_ _\\_

_⟨×⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨×⟩ Q) (x , y) = x ∈ P × y ∈ Q

_⟨⊙⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨⊙⟩ Q) (x , y) = x ∈ P ⊎ y ∈ Q

_⟨⊎⟩_ : ∀ {a b ℓ} {A : Set a} {B : Set b} →
        Pred A ℓ → Pred B ℓ → Pred (A ⊎ B) _
P ⟨⊎⟩ Q = [ P , Q ]

_⟨→⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b} →
        Pred A ℓ₁ → Pred B ℓ₂ → Pred (A → B) _
(P ⟨→⟩ Q) f = P ⊆ Q ∘ f

_⟨·⟩_ : ∀ {a b ℓ₁ ℓ₂} {A : Set a} {B : Set b}
        (P : Pred A ℓ₁) (Q : Pred B ℓ₂) →
        (P ⟨×⟩ (P ⟨→⟩ Q)) ⊆ Q ∘ uncurry (flip _$_)
(P ⟨·⟩ Q) (p , f) = f p

-- Converse.

_~ : ∀ {a b ℓ} {A : Set a} {B : Set b} →
     Pred (A × B) ℓ → Pred (B × A) ℓ
P ~ = P ∘ swap

-- Composition.

_⟨∘⟩_ : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c} →
        Pred (A × B) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × C) _
(P ⟨∘⟩ Q) (x , z) = ∃ λ y → (x , y) ∈ P × (y , z) ∈ Q

-- Post and pre-division.

_//_ : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c} →
       Pred (A × C) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × B) _
(P // Q) (x , y) = Q ∘ _,_ y ⊆ P ∘ _,_ x

_\\_ : ∀ {a b c ℓ₁ ℓ₂} {A : Set a} {B : Set b} {C : Set c} →
       Pred (A × C) ℓ₁ → Pred (A × B) ℓ₂ → Pred (B × C) _
P \\ Q = (P ~ // Q ~) ~
