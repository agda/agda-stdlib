------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for reflected syntax
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Instances where

open import Level

import Reflection.Literal as Literal
import Reflection.Name as Name
import Reflection.Meta as Meta
import Reflection.Abstraction as Abstraction
import Reflection.Argument as Argument
import Reflection.Argument.Visibility as Visibility
import Reflection.Argument.Relevance as Relevance
import Reflection.Argument.Information as Information
import Reflection.Pattern as Pattern
import Reflection.Term as Term

open import Relation.Binary.PropositionalEquality.Core
open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

private
  variable
    a : Level
    A : Set a

instance
  lit≡-isDecEquivalence = isDecEquivalence Literal._≟_
  name≡-isDecEquivalence = isDecEquivalence Name._≟_
  meta≡-isDecEquivalence = isDecEquivalence Meta._≟_
  visibility≡-isDecEquivalence = isDecEquivalence Visibility._≟_
  relevance≡-isDecEquivalence = isDecEquivalence Relevance._≟_
  argInfo≡-isDecEquivalence = isDecEquivalence Information._≟_
  pattern≡-isDecEquivalence = isDecEquivalence Pattern._≟_
  clause≡-isDecEquivalence = isDecEquivalence Term._≟-Clause_
  term≡-isDecEquivalence = isDecEquivalence Term._≟_
  sort≡-isDecEquivalence = isDecEquivalence Term._≟-Sort_

  abs≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = Abstraction.Abs A} _≡_
  abs≡-isDecEquivalence = isDecEquivalence (Abstraction.≡-dec _≟_)

  arg≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = Argument.Arg A} _≡_
  arg≡-isDecEquivalence = isDecEquivalence (Argument.≡-dec _≟_)
