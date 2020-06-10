------------------------------------------------------------------------
-- The Agda standard library
--
-- Arguments used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Argument where

open import Data.List.Base as List using (List; []; _∷_)
open import Data.Product using (_×_; _,_; uncurry; <_,_>)
open import Data.Nat using (ℕ)
open import Reflection.Argument.Visibility
open import Reflection.Argument.Relevance
open import Reflection.Argument.Information as Information
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Level

private
  variable
    a b : Level
    A B : Set a

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (Arg)
open Arg public

-- Pattern synonyms

pattern vArg ty = arg (arg-info visible relevant)   ty
pattern hArg ty = arg (arg-info hidden relevant)    ty
pattern iArg ty = arg (arg-info instance′ relevant) ty

------------------------------------------------------------------------
-- Lists of arguments

Args : {a : Level} (A : Set a) → Set a
Args A = List (Arg A)

infixr 5 _⟨∷⟩_ _⟅∷⟆_
pattern _⟨∷⟩_ x xs = vArg x ∷ xs
pattern _⟅∷⟆_ x xs = hArg x ∷ xs

------------------------------------------------------------------------
-- Operations

map : (A → B) → Arg A → Arg B
map f (arg i x) = arg i (f x)

map-Args : (A → B) → Args A → Args B
map-Args f xs = List.map (map f) xs

------------------------------------------------------------------------
-- Decidable equality

arg-injective₁ : ∀ {i i′} {a a′ : A} → arg i a ≡ arg i′ a′ → i ≡ i′
arg-injective₁ refl = refl

arg-injective₂ : ∀ {i i′} {a a′ : A} → arg i a ≡ arg i′ a′ → a ≡ a′
arg-injective₂ refl = refl

arg-injective : ∀ {i i′} {a a′ : A} → arg i a ≡ arg i′ a′ → i ≡ i′ × a ≡ a′
arg-injective = < arg-injective₁ , arg-injective₂ >

-- We often need decidability of equality for Arg A when implementing it
-- for A. Unfortunately ≡-dec makes the termination checker unhappy.
-- Instead, we can match on both Arg A and use unArg-dec for an obviously
-- decreasing recursive call.

unArg : Arg A → A
unArg (arg i a) = a

unArg-dec : {x y : Arg A} → Dec (unArg x ≡ unArg y) → Dec (x ≡ y)
unArg-dec {x = arg i a} {arg i′ a′} a≟a′ =
  Dec.map′ (uncurry (cong₂ arg)) arg-injective ((i Information.≟ i′) ×-dec a≟a′)

≡-dec : DecidableEquality A → DecidableEquality (Arg A)
≡-dec _≟_ x y = unArg-dec (unArg x ≟ unArg y)
