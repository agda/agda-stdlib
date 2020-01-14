------------------------------------------------------------------------
-- The Agda standard library
--
-- Abstractions used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Abstraction where

open import Data.List.Base as List using (List)
open import Data.Product using (_×_; _,_; uncurry; <_,_>)
import Data.String as String
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

private
  variable
    A B : Set

------------------------------------------------------------------------
-- Re-exporting the builtins publically

open import Agda.Builtin.Reflection public using (Abs)
open Abs public

-- Pattern synonyms

------------------------------------------------------------------------
-- Operations

map : (A → B) → Abs A → Abs B
map f (abs s x) = abs s (f x)

------------------------------------------------------------------------
-- Decidable equality

abs-injective₁ : ∀ {i i′} {a a′ : A} → abs i a ≡ abs i′ a′ → i ≡ i′
abs-injective₁ refl = refl

abs-injective₂ : ∀ {i i′} {a a′ : A} → abs i a ≡ abs i′ a′ → a ≡ a′
abs-injective₂ refl = refl

abs-injective : ∀ {i i′} {a a′ : A} → abs i a ≡ abs i′ a′ → i ≡ i′ × a ≡ a′
abs-injective = < abs-injective₁ , abs-injective₂ >

-- We often need decidability of equality for Abs A when implementing it
-- for A. Unfortunately ≡-dec makes the termination checker unhappy.
-- Instead, we can match on both Abs A and use unAbs-dec for an obviously
-- decreasing recursive call.

unAbs : Abs A → A
unAbs (abs s a) = a

unAbs-dec : {x y : Abs A} → Dec (unAbs x ≡ unAbs y) → Dec (x ≡ y)
unAbs-dec {x = abs i a} {abs i′ a′} a≟a′ =
  Dec.map′ (uncurry (cong₂ abs)) abs-injective ((i String.≟ i′) ×-dec a≟a′)

≡-dec : Decidable {A = A} _≡_ → Decidable {A = Abs A} _≡_
≡-dec _≟_ x y = unAbs-dec (unAbs x ≟ unAbs y)
