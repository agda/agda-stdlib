------------------------------------------------------------------------
-- The Agda standard library
--
-- The basic code for equational reasoning with a single relation
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Level using (_⊔_)
open import Function.Base using (case_of_)
open import Relation.Binary.Core using (Rel; _⇒_)
open import Relation.Binary.Definitions using (Reflexive; Transitive; Trans)
open import Relation.Binary.PropositionalEquality.Core as ≡ using (_≡_)
open import Relation.Binary.Reasoning.Syntax

module Relation.Binary.Reasoning.Base.Single
  {a ℓ} {A : Set a} (_∼_ : Rel A ℓ)
  (refl : Reflexive _∼_) (trans : Transitive _∼_)
  where

------------------------------------------------------------------------
-- Definition of "related to"

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

infix 4 _IsRelatedTo_

data _IsRelatedTo_ (x y : A) : Set ℓ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

start : _IsRelatedTo_ ⇒ _∼_
start (relTo x∼y) = x∼y

∼-go : Trans _∼_ _IsRelatedTo_ _IsRelatedTo_
∼-go x∼y (relTo y∼z) = relTo (trans x∼y y∼z)

≡-go : Trans _≡_ _IsRelatedTo_ _IsRelatedTo_
≡-go x≡y (relTo y∼z) = relTo (case x≡y of λ where ≡.refl → y∼z)

stop : Reflexive _IsRelatedTo_
stop = relTo refl

------------------------------------------------------------------------
-- Reasoning combinators

open begin-syntax _IsRelatedTo_ start public
open ≡-syntax _IsRelatedTo_ ≡-go public
open ∼-syntax _IsRelatedTo_ _IsRelatedTo_ ∼-go public
open end-syntax _IsRelatedTo_ stop public
