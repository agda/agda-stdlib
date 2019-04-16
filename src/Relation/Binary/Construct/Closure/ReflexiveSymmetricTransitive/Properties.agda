------------------------------------------------------------------------
-- The Agda standard library
--
-- Some properties of reflexive symmetric transitive closures.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Relation.Binary.Construct.Closure.ReflexiveSymmetricTransitive.Properties where

open import Data.Sum as Sum using (inj₁; inj₂)
open import Function using (_∘′_)
open import Relation.Binary.Core
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive as RTrans

module _ {a ℓ} {A : Set a} {_⟶_ : Rel A ℓ} where

  private
    _—↠_ = Star _⟶_
    _↔_  = EqClosure _⟶_

  a—↠b⇒a↔b : ∀ {a b} → a —↠ b → a ↔ b
  a—↠b⇒a↔b = RTrans.map inj₁

  a—↠b⇒b↔a : ∀ {a b} → a —↠ b → b ↔ a
  a—↠b⇒b↔a = RTrans.reverse (symmetric _⟶_) ∘′ a—↠b⇒a↔b

  a—↠b&a—↠c⇒b↔c : ∀ {a b c} → a —↠ b → a —↠ c → b ↔ c
  a—↠b&a—↠c⇒b↔c a—↠b b—↠c = a—↠b⇒b↔a a—↠b ◅◅ a—↠b⇒a↔b b—↠c
