------------------------------------------------------------------------
-- The Agda standard library
--
-- Unary relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Unary where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤)
open import Data.Product.Base using (_×_; _,_; Σ-syntax; ∃; uncurry; swap)
open import Data.Sum.Base using (_⊎_; [_,_])
open import Function.Base using (_∘_; _|>_)
open import Level using (Level; _⊔_; 0ℓ; suc; Lift)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Relation.Nullary as Nullary using (¬_; Dec; True)

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
-- Explicitly not level polymorphic as this often causes unsolved metas;
-- see `Relation.Unary.Polymorphic` for a level-polymorphic version.

∅ : Pred A 0ℓ
∅ = λ _ → ⊥

-- The singleton set.

｛_｝ : A → Pred A _
｛ x ｝ = x ≡_

-- The universal set.
-- Explicitly not level polymorphic (see comments for `∅` for more details)

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

infix 4 _⊆_ _⊇_ _⊈_ _⊉_ _⊂_ _⊃_ _⊄_ _⊅_ _≐_ _≐′_

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

_≐_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ≐ Q = (P ⊆ Q) × (Q ⊆ P)

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

_≐′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ≐′ Q = (P ⊆′ Q) × (Q ⊆′ P)

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

-- Irrelevance - any two proofs that an element satifies P are
-- indistinguishable.

Irrelevant : Pred A ℓ → Set _
Irrelevant P = ∀ {x} → Nullary.Irrelevant (P x)

-- Recomputability - we can rebuild a relevant proof given an
-- irrelevant one.

Recomputable : Pred A ℓ → Set _
Recomputable P = ∀ {x} → Nullary.Recomputable (P x)

-- Stability - instances of P are stable wrt double negation

Stable : Pred A ℓ → Set _
Stable P = ∀ x → Nullary.Stable (P x)

-- Weak Decidability

WeaklyDecidable : Pred A ℓ → Set _
WeaklyDecidable P = ∀ x → Nullary.WeaklyDecidable (P x)

-- Decidability - it is possible to determine if an arbitrary element
-- satisfies P.

Decidable : Pred A ℓ → Set _
Decidable P = ∀ x → Dec (P x)

-- Erasure: A decidable predicate gives rise to another one, more
-- amenable to η-expansion

⌊_⌋ : {P : Pred A ℓ} → Decidable P → Pred A ℓ
⌊ P? ⌋ a = Lift _ (True (P? a))

-- Uniqueness

module _ (_≈_ : A → A → Set ℓ₁) (P : Pred A ℓ₂) where

  Unique : Pred A _
  Unique x = ∀ {z} → P z → z ≈ x

  UniqueSuchThat : Pred A _
  UniqueSuchThat x = P x × Unique x

------------------------------------------------------------------------
-- Operations on sets

infix 10 ⋃ ⋂
infixr 9 _⊢_ ⟨_⟩⊢_ [_]⊢_
infixr 8 _⇒_
infixr 7 _∩_
infixr 6 _∪_
infixr 6 _∖_
infix 4 _≬_ _⊥_ _⊥′_

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

-- Difference.

_∖_ : Pred A ℓ₁ → Pred A ℓ₂ → Pred A _
P ∖ Q = λ x → x ∈ P × x ∉ Q

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

-- Disjoint

_⊥_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊥ Q = P ∩ Q ⊆ ∅

_⊥′_ : Pred A ℓ₁ → Pred A ℓ₂ → Set _
P ⊥′ Q = P ∩ Q ⊆′ ∅

-- Update/preimage/inverse image/functorial change-of-base
--
-- The notation, which elsewhere might be rendered
-- * `f⁻¹ P`, for preimage/inverse image
-- * `f* P`, for change-of-base/pullback along `f`
-- captures the Martin-Löf tradition of only mentioning updates to
-- the ambient context when describing a context-indexed family P:
-- e.g. (_, σ) ⊢ Tm τ is
-- "a term of type τ in the ambient context extended with a fresh σ".

_⊢_ : (A → B) → Pred B ℓ → Pred A ℓ
f ⊢ P = λ x → P (f x)

-- Change-of-base has left- and right- adjoints (Lawvere).
--
-- We borrow the 'diamond'/'box' notation from modal logic, cf.
-- `Relation.Unary.Closure.Base`, rather than Lawvere's ∃f, ∀f.
-- In some settings (eg statistics/probability), the left adjoint
-- is called 'image' or 'pushforward', but the right adjoint
-- doesn't seem to have a non-symbolic name.

-- Diamond

⟨_⟩⊢_ : (A → B) → Pred A ℓ → Pred B _
⟨ f ⟩⊢ P = λ y → ∃ λ x → f x ≡ y × P x

-- Box

[_]⊢_ : (A → B) → Pred A ℓ → Pred B _
[ f ]⊢ P = λ y → ∀ {x} → f x ≡ y → P x

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
        (P ⟨×⟩ (P ⟨→⟩ Q)) ⊆ Q ∘ uncurry _|>_
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
