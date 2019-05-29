------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Decidable where

open import Data.Bool.Base using (Bool; false; true; not; T)
open import Data.Empty
open import Data.Product hiding (map)
open import Data.Unit
open import Function
open import Function.Equality using (_⟨$⟩_; module Π)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Function.Injection using (Injection; module Injection)
open import Level using (Level; Lift)
open import Relation.Binary using (Setoid; module Setoid; Decidable)
open import Agda.Builtin.Equality
open import Relation.Nullary

private
  variable
    p q : Level
    P : Set p
    Q : Set q

------------------------------------------------------------------------
-- Conversion to and from Bool

⌊_⌋ : Dec P → Bool
⌊ yes _ ⌋ = true
⌊ no  _ ⌋ = false

------------------------------------------------------------------------
-- Types for whether a type is occupied or not

True : Dec P → Set
True Q = T ⌊ Q ⌋

False : Dec P → Set
False Q = T (not ⌊ Q ⌋)

-- Gives a witness to the "truth".

toWitness : ∀ {Q : Dec P} → True Q → P
toWitness {Q = yes p} _  = p

-- Establishes a "truth", given a witness.

fromWitness : ∀ {Q : Dec P} → P → True Q
fromWitness {Q = yes p} = const _
fromWitness {Q = no ¬p} = ¬p

-- Variants for False.

toWitnessFalse : ∀ {Q : Dec P} → False Q → ¬ P
toWitnessFalse {Q = no  ¬p} _  = ¬p

fromWitnessFalse : ∀ {Q : Dec P} → ¬ P → False Q
fromWitnessFalse {Q = yes p} = flip _$_ p
fromWitnessFalse {Q = no ¬p} = const _

------------------------------------------------------------------------
-- Maps

map : P ⇔ Q → Dec P → Dec Q
map P⇔Q (yes p) = yes (Equivalence.to P⇔Q ⟨$⟩ p)
map P⇔Q (no ¬p) = no (¬p ∘ _⟨$⟩_ (Equivalence.from P⇔Q))

map′ : (P → Q) → (Q → P) → Dec P → Dec Q
map′ P→Q Q→P = map (equivalence P→Q Q→P)

module _ {a₁ a₂ b₁ b₂} {A : Setoid a₁ a₂} {B : Setoid b₁ b₂} where

  open Injection
  open Setoid A using () renaming (_≈_ to _≈A_)
  open Setoid B using () renaming (_≈_ to _≈B_)

  -- If there is an injection from one setoid to another, and the
  -- latter's equivalence relation is decidable, then the former's
  -- equivalence relation is also decidable.

  via-injection : Injection A B → Decidable _≈B_ → Decidable _≈A_
  via-injection inj dec x y with dec (to inj ⟨$⟩ x) (to inj ⟨$⟩ y)
  ... | yes injx≈injy = yes (Injection.injective inj injx≈injy)
  ... | no  injx≉injy = no (λ x≈y → injx≉injy (Π.cong (to inj) x≈y))

------------------------------------------------------------------------
-- Extracting proofs

module _ {p} {P : Set p} where

-- If a decision procedure returns "yes", then we can extract the
-- proof using from-yes.

  From-yes : Dec P → Set p
  From-yes (yes _) = P
  From-yes (no  _) = Lift p ⊤

  from-yes : (p : Dec P) → From-yes p
  from-yes (yes p) = p
  from-yes (no  _) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.

  From-no : Dec P → Set p
  From-no (no  _) = ¬ P
  From-no (yes _) = Lift p ⊤

  from-no : (p : Dec P) → From-no p
  from-no (no ¬p) = ¬p
  from-no (yes _) = _

------------------------------------------------------------------------
-- Result of decidability

dec-yes : (p? : Dec P) → P → ∃ λ p′ → p? ≡ yes p′
dec-yes (yes p′) p = p′ , refl
dec-yes (no ¬p) p = ⊥-elim (¬p p)

dec-no : (p? : Dec P) → ¬ P → ∃ λ ¬p′ → p? ≡ no ¬p′
dec-no (yes p) ¬p  = ¬p , ⊥-elim (¬p p)
dec-no (no ¬p′) ¬p = ¬p′ , refl

dec-yes-irr : (p? : Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
dec-yes-irr p? irr p with dec-yes p? p
... | p′ , eq rewrite irr p p′ = eq
