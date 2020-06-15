------------------------------------------------------------------------
-- The Agda standard library
--
-- Patterns used in the reflection machinery
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Pattern where

open import Data.List.Base hiding (_++_)
open import Data.List.Properties
import Data.Nat as Nat
open import Data.Product
open import Data.String as String using (String; braces; parens; _++_; _<+>_)
import Reflection.Literal as Literal
import Reflection.Name as Name
open import Relation.Nullary
open import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Product using (_×-dec_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Reflection.Argument
open import Reflection.Argument.Visibility using (Visibility); open Visibility
open import Reflection.Argument.Relevance using (Relevance); open Relevance
open import Reflection.Argument.Information using (ArgInfo); open ArgInfo

------------------------------------------------------------------------
-- Re-exporting the builtin type and constructors

open import Agda.Builtin.Reflection public using (Pattern)
open Pattern public

------------------------------------------------------------------------
-- Re-exporting definitions that used to be here

open import Reflection.Term
  using    ( proj-injective )
  renaming ( pat-con-injective₁ to con-injective₁
           ; pat-con-injective₂ to con-injective₂
           ; pat-con-injective  to con-injective
           ; pat-var-injective  to var-injective
           ; pat-lit-injective  to lit-injective
           ; _≟-Patterns_       to _≟s_
           ; _≟-Pattern_        to _≟_
           )
  public
