------------------------------------------------------------------------
-- The Agda standard library
--
-- Sum combinators for propositional equality preserving functions
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Data.Sum.Function.Propositional where

open import Data.Sum.Base using (_⊎_)
open import Data.Sum.Function.Setoid
  using (_⊎-function_; _⊎-equivalence_; _⊎-injection_; _⊎-surjection_
        ; _⊎-leftInverse_; _⊎-rightInverse_; _⊎-bijection_; _⊎-inverse_)
open import Data.Sum.Relation.Binary.Pointwise using (Pointwise-≡↔≡; _⊎ₛ_)
open import Function.Construct.Composition as Compose
open import Function.Related.Propositional
  using (_∼[_]_; implication; reverseImplication; equivalence; injection;
    reverseInjection; leftInverse; surjection; bijection)
open import Function.Base using (id)
open import Function.Bundles
  using (Inverse; _⟶_; _⇔_; _↣_; _↠_; _↩_; _↪_; _⤖_; _↔_)
open import Function.Properties.Inverse as Inv
  using (Inverse⇒Equivalence; Inverse⇒Bijection; Inverse⇒Injection
        ; Inverse⇒Surjection)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality.Properties using (setoid)

private
  variable
    a b c d : Level
    A B C D : Set a


------------------------------------------------------------------------
-- Helper lemma

private
  liftViaInverse : {R : ∀ {a b ℓ₁ ℓ₂} → REL (Setoid a ℓ₁) (Setoid b ℓ₂) (a ⊔ b ⊔ ℓ₁ ⊔ ℓ₂)} →
                   (∀ {a b c ℓ₁ ℓ₂ ℓ₃} {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} {U : Setoid c ℓ₃} → R S T → R T U → R S U) →
                   (∀ {a b ℓ₁ ℓ₂} {S : Setoid a ℓ₁} {T : Setoid b ℓ₂} → Inverse S T → R S T) →
                   (R (setoid A) (setoid C) → R (setoid B) (setoid D) → R (setoid A ⊎ₛ setoid B) (setoid C ⊎ₛ setoid D)) →
                   R (setoid A) (setoid C) → R (setoid B) (setoid D) →
                   R (setoid (A ⊎ B)) (setoid (C ⊎ D))
  liftViaInverse trans inv⇒R lift RAC RBD =
    Inv.transportVia trans inv⇒R (Inv.sym (Pointwise-≡↔≡ _ _)) (lift RAC RBD) (Pointwise-≡↔≡ _ _)

------------------------------------------------------------------------
-- Combinators for various function types

infixr 1 _⊎-⟶_ _⊎-⇔_ _⊎-↣_ _⊎-↩_ _⊎-↪_ _⊎-↔_

_⊎-⟶_ : A ⟶ B → C ⟶ D → (A ⊎ C) ⟶ (B ⊎ D)
_⊎-⟶_ = liftViaInverse Compose.function Inv.toFunction _⊎-function_


_⊎-⇔_ : A ⇔ B → C ⇔ D → (A ⊎ C) ⇔ (B ⊎ D)
_⊎-⇔_ = liftViaInverse Compose.equivalence Inverse⇒Equivalence _⊎-equivalence_

_⊎-↣_ : A ↣ B → C ↣ D → (A ⊎ C) ↣ (B ⊎ D)
_⊎-↣_ = liftViaInverse Compose.injection Inverse⇒Injection _⊎-injection_

_⊎-↠_ : A ↠ B → C ↠ D → (A ⊎ C) ↠ (B ⊎ D)
_⊎-↠_ = liftViaInverse Compose.surjection Inverse⇒Surjection _⊎-surjection_

_⊎-↩_ : A ↩ B → C ↩ D → (A ⊎ C) ↩ (B ⊎ D)
_⊎-↩_ = liftViaInverse Compose.leftInverse Inverse.leftInverse _⊎-leftInverse_

_⊎-↪_ : A ↪ B → C ↪ D → (A ⊎ C) ↪ (B ⊎ D)
_⊎-↪_ = liftViaInverse Compose.rightInverse Inverse.rightInverse _⊎-rightInverse_

_⊎-⤖_ : A ⤖ B → C ⤖ D → (A ⊎ C) ⤖ (B ⊎ D)
_⊎-⤖_ = liftViaInverse Compose.bijection Inverse⇒Bijection _⊎-bijection_

_⊎-↔_ : A ↔ B → C ↔ D → (A ⊎ C) ↔ (B ⊎ D)
_⊎-↔_ = liftViaInverse Compose.inverse id _⊎-inverse_

infixr 1 _⊎-cong_

_⊎-cong_ : ∀ {k} → A ∼[ k ] B → C ∼[ k ] D → (A ⊎ C) ∼[ k ] (B ⊎ D)
_⊎-cong_ {k = implication}         = _⊎-⟶_
_⊎-cong_ {k = reverseImplication}  = _⊎-⟶_
_⊎-cong_ {k = equivalence}         = _⊎-⇔_
_⊎-cong_ {k = injection}           = _⊎-↣_
_⊎-cong_ {k = reverseInjection}    = _⊎-↣_
_⊎-cong_ {k = leftInverse}         = _⊎-↪_
_⊎-cong_ {k = surjection}          = _⊎-↠_
_⊎-cong_ {k = bijection}           = _⊎-↔_
