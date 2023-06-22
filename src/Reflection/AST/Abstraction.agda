------------------------------------------------------------------------
-- The Agda standard library
--
-- Abstractions used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Abstraction where

open import Data.Product                               using (_×_; <_,_>; uncurry)
open import Data.String as String                      using (String)
open import Level
open import Relation.Nullary.Decidable                 using (Dec; map′; _×-dec_)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong₂)

private
  variable
    a b : Level
    A B : Set a
    s t : String
    x y : A

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public
  using (Abs)

open Abs public

------------------------------------------------------------------------
-- Operations

map : (A → B) → Abs A → Abs B
map f (abs s x) = abs s (f x)

------------------------------------------------------------------------
-- Decidable equality

abs-injective₁ : abs s x ≡ abs t y → s ≡ t
abs-injective₁ refl = refl

abs-injective₂ : abs s x ≡ abs t y → x ≡ y
abs-injective₂ refl = refl

abs-injective : abs s x ≡ abs t y → s ≡ t × x ≡ y
abs-injective = < abs-injective₁ , abs-injective₂ >

-- We often need decidability of equality for Abs A when implementing it
-- for A. Unfortunately ≡-dec makes the termination checker unhappy.
-- Instead, we can match on both Abs A and use unAbs-dec for an obviously
-- decreasing recursive call.

unAbs : Abs A → A
unAbs (abs s a) = a

unAbs-dec : {abs1 abs2 : Abs A} → Dec (unAbs abs1 ≡ unAbs abs2) → Dec (abs1 ≡ abs2)
unAbs-dec {abs1 = abs s a} {abs t a′} a≟a′ =
  map′ (uncurry (cong₂ abs)) abs-injective (s String.≟ t ×-dec a≟a′)

≡-dec : DecidableEquality A → DecidableEquality (Abs A)
≡-dec _≟_ x y = unAbs-dec (unAbs x ≟ unAbs y)
