------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent product combinators for propositional equality
-- preserving functions
------------------------------------------------------------------------

{-# OPTIONS --with-K --safe #-}

module Data.Product.Function.Dependent.Propositional.WithK where

open import Data.Product.Base
open import Data.Product.Properties
open import Data.Product.Function.Dependent.Setoid
open import Data.Product.Relation.Binary.Pointwise.Dependent
open import Data.Product.Relation.Binary.Pointwise.Dependent.WithK
open import Level using (Level)
open import Function
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    i a : Level
    I J : Set i
    A B : I → Set a
    
------------------------------------------------------------------------
-- Combinator for Injection

module _ where
  open Injection
  
  ↣ : (I↣J : I ↣ J) →
      (∀ {x} → A x ↣ B (to I↣J x)) →
      Σ I A ↣ Σ J B
  ↣ {I = I} {J = J} {A = A} {B = B} I↣J A↣B = mk↣ to′-injective
    where

    to′ : Σ I A → Σ J B
    to′ = map (to I↣J) (to A↣B)

    to′-injective : Injective _≡_ _≡_ to′
    to′-injective eq = ?
  {-

with Σ-≡,≡←≡ eq
    ... | (eq1 , eq2) = Σ-≡,≡→≡ (injective I↣J eq1 , {!!})
    injection Pointwise-≡↔≡ ⟨∘⟩
    injection (H.indexedSetoid B) I↣J
      (Inverse.injection (H.≡↔≅ B) ⟨∘⟩
       A↣B ⟨∘⟩
       Inverse.injection (Inv.sym (H.≡↔≅ A))) ⟨∘⟩
    Inverse.injection (Inv.sym Pointwise-≡↔≡)
    where open Injection using () renaming (_∘_ to _⟨∘⟩_)
  -}
