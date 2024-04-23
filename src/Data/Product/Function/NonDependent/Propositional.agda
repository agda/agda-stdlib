------------------------------------------------------------------------
-- The Agda standard library
--
-- Non-dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Data.Product.Function.NonDependent.Propositional where

open import Data.Product.Base using (_×_; map)
open import Data.Product.Function.NonDependent.Setoid
open import Data.Product.Relation.Binary.Pointwise.NonDependent
  using (_×ₛ_; Pointwise-≡↔≡)
open import Function.Base using (id)
open import Function.Bundles
  using (Inverse; _⟶_; _⇔_; _↣_; _↠_; _⤖_; _↩_; _↪_; _↔_)
open import Function.Properties.Inverse as Inv
  using (Inverse⇒Equivalence; Inverse⇒Injection; Inverse⇒Surjection;
         Inverse⇒Bijection)
open import Function.Related.Propositional
  using (_∼[_]_; implication; reverseImplication; equivalence; injection;
         reverseInjection; leftInverse; surjection; bijection)
import Function.Construct.Composition as Compose
open import Level using (Level; _⊔_)
open import Relation.Binary hiding (_⇔_)
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
                   (R (setoid A) (setoid C) → R (setoid B) (setoid D) → R (setoid A ×ₛ setoid B) (setoid C ×ₛ setoid D)) →
                   R (setoid A) (setoid C) → R (setoid B) (setoid D) →
                   R (setoid (A × B)) (setoid (C × D))
  liftViaInverse trans inv⇒R lift RAC RBD =
    Inv.transportVia trans inv⇒R (Inv.sym Pointwise-≡↔≡) (lift RAC RBD) Pointwise-≡↔≡

------------------------------------------------------------------------
-- Combinators for various function types

infixr 2 _×-⟶_ _×-⇔_ _×-↣_ _×-↠_ _×-⤖_ _×-↩_ _×-↪_ _×-↔_

_×-⟶_ : A ⟶ B → C ⟶ D → (A × C) ⟶ (B × D)
_×-⟶_ = liftViaInverse Compose.function Inv.toFunction _×-function_

_×-⇔_ : A ⇔ B → C ⇔ D → (A × C) ⇔ (B × D)
_×-⇔_ = liftViaInverse Compose.equivalence Inverse⇒Equivalence _×-equivalence_

_×-↣_ : A ↣ B → C ↣ D → (A × C) ↣ (B × D)
_×-↣_ = liftViaInverse Compose.injection Inverse⇒Injection _×-injection_

_×-↠_ : A ↠ B → C ↠ D → (A × C) ↠ (B × D)
_×-↠_ = liftViaInverse Compose.surjection Inverse⇒Surjection _×-surjection_

_×-⤖_ : A ⤖ B → C ⤖ D → (A × C) ⤖ (B × D)
_×-⤖_ = liftViaInverse Compose.bijection Inverse⇒Bijection _×-bijection_

_×-↩_ : A ↩ B → C ↩ D → (A × C) ↩ (B × D)
_×-↩_ = liftViaInverse Compose.leftInverse Inverse.leftInverse _×-leftInverse_

_×-↪_ : A ↪ B → C ↪ D → (A × C) ↪ (B × D)
_×-↪_ = liftViaInverse Compose.rightInverse Inverse.rightInverse _×-rightInverse_

_×-↔_ : A ↔ B → C ↔ D → (A × C) ↔ (B × D)
_×-↔_ = liftViaInverse Compose.inverse id _×-inverse_

infixr 2 _×-cong_

_×-cong_ : ∀ {k} → A ∼[ k ] B → C ∼[ k ] D → (A × C) ∼[ k ] (B × D)
_×-cong_ {k = implication}         = _×-⟶_
_×-cong_ {k = reverseImplication}  = _×-⟶_
_×-cong_ {k = equivalence}         = _×-⇔_
_×-cong_ {k = injection}           = _×-↣_
_×-cong_ {k = reverseInjection}    = _×-↣_
_×-cong_ {k = leftInverse}         = _×-↪_
_×-cong_ {k = surjection}          = _×-↠_
_×-cong_ {k = bijection}           = _×-↔_
