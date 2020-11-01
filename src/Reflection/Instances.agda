------------------------------------------------------------------------
-- The Agda standard library
--
-- Instances for reflected syntax
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Reflection.Instances where

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

open import Relation.Binary.PropositionalEquality.Properties
  using (isDecEquivalence)
open import Relation.Binary.TypeClasses

instance
  ≡-isDecEquivalence-Lit = isDecEquivalence Literal._≟_
  ≡-isDecEquivalence-Name = isDecEquivalence Name._≟_
  ≡-isDecEquivalence-Meta = isDecEquivalence Meta._≟_
  ≡-isDecEquivalence-Visibility = isDecEquivalence Visibility._≟_
  ≡-isDecEquivalence-Relevance = isDecEquivalence Relevance._≟_
  ≡-isDecEquivalence-Arg-info = isDecEquivalence Information._≟_
  ≡-isDecEquivalence-Pattern = isDecEquivalence Pattern._≟_
  ≡-isDecEquivalence-Abs = λ {ℓ} {A} {{≡-isDecEquivalence-A}} → isDecEquivalence (Abstraction.≡-dec {ℓ} {A} (_≟_ {{≡-isDecEquivalence-A}}))
  ≡-isDecEquivalence-Arg = λ {ℓ} {A} {{≡-isDecEquivalence-A}} → isDecEquivalence (Argument.≡-dec {ℓ} {A} (_≟_ {{≡-isDecEquivalence-A}}))
  ≡-isDecEquivalence-Clause = isDecEquivalence Term._≟-Clause_
  ≡-isDecEquivalence-Term = isDecEquivalence Term._≟_
  ≡-isDecEquivalence-Sort = isDecEquivalence Term._≟-Sort_
