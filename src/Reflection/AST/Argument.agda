------------------------------------------------------------------------
-- The Agda standard library
--
-- Arguments used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Reflection.AST.Argument where

open import Data.List.Base as List                     using (List; []; _∷_)
open import Data.Product                               using (_×_; <_,_>; uncurry)
open import Relation.Nullary.Decidable                 using (Dec; map′; _×-dec_)
open import Relation.Binary                            using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong₂)
open import Level

open import Reflection.AST.Argument.Visibility
open import Reflection.AST.Argument.Relevance
open import Reflection.AST.Argument.Quantity
open import Reflection.AST.Argument.Modality
open import Reflection.AST.Argument.Information as Information

private
  variable
    a b : Level
    A B : Set a
    i j : ArgInfo
    x y : A

------------------------------------------------------------------------
-- Re-exporting the builtins publicly

open import Agda.Builtin.Reflection public using (Arg)
open Arg public

-- Pattern synonyms

pattern defaultModality = modality relevant quantity-ω

pattern vArg ty = arg (arg-info visible   defaultModality) ty
pattern hArg ty = arg (arg-info hidden    defaultModality) ty
pattern iArg ty = arg (arg-info instance′ defaultModality) ty

------------------------------------------------------------------------
-- Lists of arguments

Args : (A : Set a) → Set a
Args A = List (Arg A)

-- Pattern for appending a visible argument
infixr 5 _⟨∷⟩_
pattern _⟨∷⟩_ x args = vArg x ∷ args

-- Pattern for appending a hidden argument
infixr 5 _⟅∷⟆_
pattern _⟅∷⟆_ x args = hArg x ∷ args

------------------------------------------------------------------------
-- Operations

map : (A → B) → Arg A → Arg B
map f (arg i x) = arg i (f x)

map-Args : (A → B) → Args A → Args B
map-Args f xs = List.map (map f) xs

------------------------------------------------------------------------
-- Decidable equality

arg-injective₁ : arg i x ≡ arg j y → i ≡ j
arg-injective₁ refl = refl

arg-injective₂ : arg i x ≡ arg j y → x ≡ y
arg-injective₂ refl = refl

arg-injective : arg i x ≡ arg j y → i ≡ j × x ≡ y
arg-injective = < arg-injective₁ , arg-injective₂ >

-- We often need decidability of equality for Arg A when implementing it
-- for A. Unfortunately ≡-dec makes the termination checker unhappy.
-- Instead, we can match on both Arg A and use unArg-dec for an obviously
-- decreasing recursive call.

unArg : Arg A → A
unArg (arg i a) = a

unArg-dec : {arg1 arg2 : Arg A} → Dec (unArg arg1 ≡ unArg arg2) → Dec (arg1 ≡ arg2)
unArg-dec {arg1 = arg i x} {arg j y} arg1≟arg2 =
  map′ (uncurry (cong₂ arg)) arg-injective (i Information.≟ j ×-dec arg1≟arg2)

≡-dec : DecidableEquality A → DecidableEquality (Arg A)
≡-dec _≟_ x y = unArg-dec (unArg x ≟ unArg y)
