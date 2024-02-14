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
open import Data.Product.Function.Dependent.Setoid using (injection)
open import Data.Product.Relation.Binary.Pointwise.Dependent
open import Data.Product.Relation.Binary.Pointwise.Dependent.WithK
open import Relation.Binary.Indexed.Heterogeneous.Construct.At using (_atₛ_)
open import Relation.Binary.HeterogeneousEquality as H
open import Level using (Level)
open import Function
open import Function.Properties.Injection
open import Function.Properties.Inverse as Inverse

private
  variable
    i a : Level
    I J : Set i
    A B : I → Set a

------------------------------------------------------------------------
-- Combinator for Injection

module _ where
  open Injection

  Σ-↣ : (I↣J : I ↣ J) →
         (∀ {i} → A i ↣ B (to I↣J i)) →
         Σ I A ↣ Σ J B
  Σ-↣ {A = A} {B = B} I↣J A↣B =
    ↣-trans (Inverse⇒Injection (Inverse.sym Pointwise-≡↔≡)) $
      ↣-trans (injection I↣J Aᵢ↣Bᵢ) $
        Inverse⇒Injection Pointwise-≡↔≡
    where
    Aᵢ↣Bᵢ : (∀ {i} → Injection (H.indexedSetoid A atₛ i) (H.indexedSetoid B atₛ (Injection.to I↣J i)))
    Aᵢ↣Bᵢ =
      ↣-trans (Inverse⇒Injection (Inverse.sym (H.≡↔≅ A))) $
        ↣-trans A↣B $
          Inverse⇒Injection (H.≡↔≅ B)
