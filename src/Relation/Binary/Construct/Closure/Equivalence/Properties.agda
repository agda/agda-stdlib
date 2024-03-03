------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of equivalence closures.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Relation.Binary.Construct.Closure.Equivalence.Properties where

open import Function.Base using (_∘′_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Construct.Closure.Equivalence
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as RTrans
import Relation.Binary.Construct.Closure.Symmetric as SymClosure

module _ {a ℓ} {A : Set a} {_⟶_ : Rel A ℓ} where

  private
    _—↠_ = Star _⟶_
    _↔_  = EqClosure _⟶_

  a—↠b⇒a↔b : ∀ {a b} → a —↠ b → a ↔ b
  a—↠b⇒a↔b = RTrans.map SymClosure.fwd

  a—↠b⇒b↔a : ∀ {a b} → a —↠ b → b ↔ a
  a—↠b⇒b↔a = symmetric _ ∘′ a—↠b⇒a↔b

  a—↠b&a—↠c⇒b↔c : ∀ {a b c} → a —↠ b → a —↠ c → b ↔ c
  a—↠b&a—↠c⇒b↔c a—↠b b—↠c = a—↠b⇒b↔a a—↠b ◅◅ a—↠b⇒a↔b b—↠c
