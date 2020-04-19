------------------------------------------------------------------------
-- The Agda standard library
--
-- Unary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary where

open import Data.Empty
open import Data.Unit.Base using (⊤)
open import Data.Product
open import Data.Sum.Base using (_⊎_; [_,_])
open import Function.Base
open import Level
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable.Core using (True)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

private
  variable
    a b c ℓ ℓ₁ ℓ₂ : Level
    A : Set a
    B : Set b
    C : Set c

------------------------------------------------------------------------
-- Definition

-- Unary relations are known as predicates and `Pred A ℓ` can be viewed
-- as some property that elements of type A might satisfy.

-- Consequently `P : Pred A ℓ` can also be seen as a subset of A
-- containing all the elements of A that satisfy property P. This view
-- informs much of the notation used below.

Pred : ∀ {a} → Set a → (ℓ : Level) → Set (a ⊔ suc ℓ)
Pred A ℓ = A → Set ℓ

------------------------------------------------------------------------
-- Special sets

-- The empty set.

∅ : Pred A 0ℓ
∅ = λ _ → ⊥

-- The singleton set.

｛_｝ : A → Pred A _
｛ x ｝ = x ≡_

-- The universal set.

U : Pred A 0ℓ
U = λ _ → ⊤

------------------------------------------------------------------------
-- Membership

infix 4 _∈_ _∉_

_∈_ : A → Pred A ℓ → Set _
x ∈ P = P x

_∉_ : A → Pred A ℓ → Set _
x ∉ P = ¬ x ∈ P

------------------------------------------------------------------------
-- Subset relations

infix 4 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_

_⊆_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊆ Q = ∀ {x} → x ∈ P → x ∈ Q

_⊇_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊇ Q = Q ⊆ P

_⊈_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊈ Q = ¬ (P ⊆ Q)

_⊉_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊉ Q = ¬ (P ⊇ Q)

_⊂_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊂ Q = P ⊆ Q × Q ⊈ P

_⊃_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊃ Q = Q ⊂ P

_⊄_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊄ Q = ¬ (P ⊂ Q)

_⊅_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊅ Q = ¬ (P ⊃ Q)

-- The following primed variants of _⊆_ can be used when 'x' can't
-- be inferred from 'x ∈ P'.

infix 4 _⊆′_ _⊇′_ _⊈′_ _⊉′_ _⊂′_ _⊃′_ _⊄′_ _⊅′_

_⊆′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊆′ Q = ∀ x → x ∈ P → x ∈ Q

_⊇′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
Q ⊇′ P = P ⊆′ Q

_⊈′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊈′ Q = ¬ (P ⊆′ Q)

_⊉′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊉′ Q = ¬ (P ⊇′ Q)

_⊂′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊂′ Q = P ⊆′ Q × Q ⊈′ P

_⊃′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊃′ Q = Q ⊂′ P

_⊄′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊄′ Q = ¬ (P ⊂′ Q)

_⊅′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊅′ Q = ¬ (P ⊃′ Q)

------------------------------------------------------------------------
-- Properties of sets

infix 10 Satisfiable Universal IUniversal

-- Emptiness - no element satisfies P.

Empty : Pred A ℓ → Set _
Empty P = ∀ x → x ∉ P

-- Satisfiable - at least one element satisfies P.

Satisfiable : Pred A ℓ → Set _
Satisfiable P = ∃ λ x → x ∈ P

syntax Satisfiable P = ∃⟨ P ⟩

-- Universality - all elements satisfy P.

Universal : Pred A ℓ → Set _
Universal P = ∀ x → x ∈ P

syntax Universal  P = Π[ P ]

-- Implicit universality - all elements satisfy P.

IUniversal : Pred A ℓ → Set _
IUniversal P = ∀ {x} → x ∈ P

syntax IUniversal P = ∀[ P ]

-- Decidability - it is possible to determine if an arbitrary element
-- satisfies P.

Decidable : Pred A ℓ → Set _
Decidable P = ∀ x → Dec (P x)

-- Erasure: A decidable predicate gives rise to another one, more
-- amenable to η-expansion

⌊_⌋ : {P : Pred A ℓ} → Decidable P → Pred A ℓ
⌊ P? ⌋ a = Lift _ (True (P? a))

-- Irrelevance - any two proofs that an element satifies P are
-- indistinguishable.

Irrelevant : Pred A ℓ → Set _
Irrelevant P = ∀ {x} (a : P x) (b : P x) → a ≡ b

-- Recomputability - we can rebuild a relevant proof given an
-- irrelevant one.

Recomputable : Pred A ℓ → Set _
Recomputable P = ∀ {x} → .(P x) → P x

------------------------------------------------------------------------
-- Operations on sets

infix 10 ⋃ ⋂
infixr 9 _⊢_
infixr 8 _⇒_
infixr 7 _∩_
infixr 6 _∪_
infix 4 _≬_

-- Complement.

∁ : Pred A ℓ → Pred A ℓ
∁ P = λ x → x ∉ P

-- Implication.

_⇒_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ⇒ Q = λ x → x ∈ P → x ∈ Q

-- Union.

_∪_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ∪ Q = λ x → x ∈ P ⊎ x ∈ Q

-- Intersection.

_∩_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ∩ Q = λ x → x ∈ P × x ∈ Q

-- Infinitary union.

⋃ : ∀ {i} (I : Set i) → (I → Pred A ℓ) → Pred A _
⋃ I P = λ x → Σ[ i ∈ I ] P i x

syntax ⋃ I (λ i → P) = ⋃[ i ∶ I ] P

-- Infinitary intersection.

⋂ : ∀ {i} (I : Set i) → (I → Pred A ℓ) → Pred A _
⋂ I P = λ x → (i : I) → P i x

syntax ⋂ I (λ i → P) = ⋂[ i ∶ I ] P

-- Positive version of non-disjointness, dual to inclusion.

_≬_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ≬ Q = ∃ λ x → x ∈ P × x ∈ Q

-- Update.

_⊢_ : (A → B) → Pred B ℓ → Pred A ℓ
f ⊢ P = λ x → P (f x)

------------------------------------------------------------------------
-- Predicate combinators

-- These differ from the set operations above, as the carrier set of the
-- resulting predicates are not the same as the carrier set of the
-- component predicates.

infixr  2 _⟨×⟩_
infixr  2 _⟨⊙⟩_
infixr  1 _⟨⊎⟩_
infixr  0 _⟨→⟩_
infixl  9 _⟨·⟩_
infix  10 _~
infixr  9 _⟨∘⟩_
infixr  2 _//_ _\\_

-- Product.

_⟨×⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨×⟩ Q) (x , y) = x ∈ P × y ∈ Q

-- Sum over one element.

_⟨⊎⟩_ : Pred A ℓ → Pred B ℓ → Pred (A ⊎ B) _
P ⟨⊎⟩ Q = [ P , Q ]

-- Sum over two elements.

_⟨⊙⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A × B) _
(P ⟨⊙⟩ Q) (x , y) = x ∈ P ⊎ y ∈ Q

-- Implication.

_⟨→⟩_ : Pred A ℓ₁ → Pred B ℓ₂ → Pred (A → B) _
(P ⟨→⟩ Q) f = P ⊆ Q ∘ f

-- Product.

_⟨·⟩_ : (P : Pred A ℓ₁) (Q : Pred B ℓ₂) →
        (P ⟨×⟩ (P ⟨→⟩ Q)) ⊆ Q ∘ uncurry (flip _$_)
(P ⟨·⟩ Q) (p , f) = f p

-- Converse.

_~ : Pred (A × B) ℓ → Pred (B × A) ℓ
P ~ = P ∘ swap

-- Composition.

_⟨∘⟩_ : Pred (A × B) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × C) _
(P ⟨∘⟩ Q) (x , z) = ∃ λ y → (x , y) ∈ P × (y , z) ∈ Q

-- Post-division.

_//_ : Pred (A × C) ℓ₁ → Pred (B × C) ℓ₂ → Pred (A × B) _
(P // Q) (x , y) = Q ∘ (y ,_) ⊆ P ∘ (x ,_)

-- Pre-division.

_\\_ : Pred (A × C) ℓ₁ → Pred (A × B) ℓ₂ → Pred (B × C) _
P \\ Q = (P ~ // Q ~) ~
