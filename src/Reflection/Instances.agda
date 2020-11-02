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
  Lit-≡-isDecEquivalence = isDecEquivalence Literal._≟_
  Name-≡-isDecEquivalence = isDecEquivalence Name._≟_
  Meta-≡-isDecEquivalence = isDecEquivalence Meta._≟_
  Visibility-≡-isDecEquivalence = isDecEquivalence Visibility._≟_
  Relevance-≡-isDecEquivalence = isDecEquivalence Relevance._≟_
  ArgInfo-≡-isDecEquivalence = isDecEquivalence Information._≟_
  Pattern-≡-isDecEquivalence = isDecEquivalence Pattern._≟_
  Clause-≡-isDecEquivalence = isDecEquivalence Term._≟-Clause_
  Term-≡-isDecEquivalence = isDecEquivalence Term._≟_
  Sort-≡-isDecEquivalence = isDecEquivalence Term._≟-Sort_

  Abs-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = Abstraction.Abs A} _≡_
  Abs-≡-isDecEquivalence = isDecEquivalence (Abstraction.≡-dec _≟_)

  Arg-≡-isDecEquivalence : {{IsDecEquivalence {A = A} _≡_}} → IsDecEquivalence {A = Argument.Arg A} _≡_
  Arg-≡-isDecEquivalence = isDecEquivalence (Argument.≡-dec _≟_)
