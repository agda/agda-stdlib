------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on and properties of decidable relations
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Nullary.Decidable where

open import Function
open import Function.Equality    using (_⟨$⟩_; module Π)
open import Function.Equivalence using (_⇔_; equivalence; module Equivalence)
open import Function.Injection   using (Injection; module Injection)
open import Relation.Binary      using (Setoid; module Setoid; Decidable)
open import Relation.Nullary

------------------------------------------------------------------------
-- Re-exporting the core definitions

open import Relation.Nullary.Decidable.Core public

module _  {p q} {P : Set p} {Q : Set q} where

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
